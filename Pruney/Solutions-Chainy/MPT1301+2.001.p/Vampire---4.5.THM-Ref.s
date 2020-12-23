%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 164 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  249 ( 649 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f99,f104,f118,f130,f137,f261,f422])).

fof(f422,plain,
    ( ~ spl3_8
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_11
    | spl3_26 ),
    inference(avatar_split_clause,[],[f421,f258,f115,f58,f63,f96])).

fof(f96,plain,
    ( spl3_8
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f63,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f58,plain,
    ( spl3_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115,plain,
    ( spl3_11
  <=> sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f258,plain,
    ( spl3_26
  <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f421,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_11
    | spl3_26 ),
    inference(forward_demodulation,[],[f412,f117])).

fof(f117,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f412,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_26 ),
    inference(resolution,[],[f260,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
              | ~ r1_tarski(X1,k7_setfam_1(X0,X2)) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f260,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f258])).

fof(f261,plain,
    ( ~ spl3_26
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | spl3_14 ),
    inference(avatar_split_clause,[],[f224,f134,f127,f101,f96,f73,f258])).

fof(f73,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f101,plain,
    ( spl3_9
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f127,plain,
    ( spl3_13
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f134,plain,
    ( spl3_14
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f224,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f75,f136,f98,f129,f103,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f103,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f129,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f98,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f136,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f137,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f131,f73,f68,f48,f134])).

fof(f48,plain,
    ( spl3_1
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f131,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f75,f50,f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f50,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f130,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f124,f73,f63,f53,f127])).

fof(f53,plain,
    ( spl3_2
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f124,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f75,f55,f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f55,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f118,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f112,f68,f115])).

fof(f112,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f63,f101])).

fof(f93,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f99,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f94,f68,f96])).

fof(f94,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f70,f45])).

fof(f76,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_tops_2(sK1,sK0)
    & v2_tops_2(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(X1,X0)
                & v2_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,sK0)
              & v2_tops_2(X2,sK0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(X1,sK0)
            & v2_tops_2(X2,sK0)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(sK1,sK0)
          & v2_tops_2(X2,sK0)
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(sK1,sK0)
        & v2_tops_2(X2,sK0)
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(sK1,sK0)
      & v2_tops_2(sK2,sK0)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v2_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f53])).

fof(f34,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f48])).

fof(f35,plain,(
    ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (29964)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (29972)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (29971)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (29961)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  % (29965)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (29963)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.54  % (29957)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.54  % (29965)Refutation not found, incomplete strategy% (29965)------------------------------
% 0.22/0.54  % (29965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29965)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29965)Memory used [KB]: 10490
% 0.22/0.54  % (29965)Time elapsed: 0.094 s
% 0.22/0.54  % (29965)------------------------------
% 0.22/0.54  % (29965)------------------------------
% 0.22/0.55  % (29963)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f423,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f99,f104,f118,f130,f137,f261,f422])).
% 0.22/0.55  fof(f422,plain,(
% 0.22/0.55    ~spl3_8 | ~spl3_4 | ~spl3_3 | ~spl3_11 | spl3_26),
% 0.22/0.55    inference(avatar_split_clause,[],[f421,f258,f115,f58,f63,f96])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    spl3_8 <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    spl3_3 <=> r1_tarski(sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    spl3_11 <=> sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    spl3_26 <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.55  fof(f421,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_11 | spl3_26)),
% 0.22/0.55    inference(forward_demodulation,[],[f412,f117])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~spl3_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f115])).
% 0.22/0.55  fof(f412,plain,(
% 0.22/0.55    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_26),
% 0.22/0.55    inference(resolution,[],[f260,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2))) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    inference(nnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2)) | spl3_26),
% 0.22/0.55    inference(avatar_component_clause,[],[f258])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    ~spl3_26 | ~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_13 | spl3_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f224,f134,f127,f101,f96,f73,f258])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    spl3_6 <=> l1_pre_topc(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    spl3_9 <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    spl3_13 <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    spl3_14 <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2)) | (~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_13 | spl3_14)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f136,f98,f129,f103,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f101])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~spl3_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f127])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f96])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | spl3_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f134])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    l1_pre_topc(sK0) | ~spl3_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f73])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ~spl3_14 | spl3_1 | ~spl3_5 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f131,f73,f68,f48,f134])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    spl3_1 <=> v2_tops_2(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | (spl3_1 | ~spl3_5 | ~spl3_6)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f50,f70,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ~v2_tops_2(sK1,sK0) | spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f48])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    spl3_13 | ~spl3_2 | ~spl3_4 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f124,f73,f63,f53,f127])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    spl3_2 <=> v2_tops_2(sK2,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | (~spl3_2 | ~spl3_4 | ~spl3_6)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f55,f65,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f63])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    v2_tops_2(sK2,sK0) | ~spl3_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f53])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    spl3_11 | ~spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f112,f68,f115])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~spl3_5),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f70,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    spl3_9 | ~spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f93,f63,f101])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f65,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl3_8 | ~spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f94,f68,f96])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f70,f45])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f30,f73])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ((~v2_tops_2(sK1,sK0) & v2_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(X1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (~v2_tops_2(X1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(sK1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ? [X2] : (~v2_tops_2(sK1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(sK1,sK0) & v2_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(X1,X0) & (v2_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f11])).
% 0.22/0.55  fof(f11,conjecture,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f31,f68])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f33,f58])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    r1_tarski(sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f34,f53])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    v2_tops_2(sK2,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ~spl3_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f35,f48])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ~v2_tops_2(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (29963)------------------------------
% 0.22/0.55  % (29963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29963)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (29963)Memory used [KB]: 11001
% 0.22/0.55  % (29963)Time elapsed: 0.021 s
% 0.22/0.55  % (29963)------------------------------
% 0.22/0.55  % (29963)------------------------------
% 0.22/0.55  % (29956)Success in time 0.191 s
%------------------------------------------------------------------------------
