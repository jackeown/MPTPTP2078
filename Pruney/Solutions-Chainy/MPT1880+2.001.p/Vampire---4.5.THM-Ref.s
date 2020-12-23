%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 322 expanded)
%              Number of leaves         :   36 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          :  662 (1484 expanded)
%              Number of equality atoms :   81 ( 139 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f124,f134,f158,f165,f170,f179,f196,f213,f224,f235,f267,f298,f302,f320,f342,f422,f470])).

fof(f470,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_44 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f468,f73])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f468,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f467,f93])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f467,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_6
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f466,f83])).

fof(f83,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f466,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_6
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f464,f88])).

fof(f88,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_6
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f464,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_44 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( sK1 != sK1
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_44 ),
    inference(superposition,[],[f47,f421])).

fof(f421,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl4_44
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f422,plain,
    ( spl4_44
    | ~ spl4_33
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f390,f339,f276,f419])).

fof(f276,plain,
    ( spl4_33
  <=> sK2(sK0,sK1) = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f339,plain,
    ( spl4_37
  <=> sK1 = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f390,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl4_33
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f278,f341])).

fof(f341,plain,
    ( sK1 = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f339])).

fof(f278,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f276])).

fof(f342,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_18
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f336,f300,f167,f131,f91,f339])).

fof(f131,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f167,plain,
    ( spl4_18
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f300,plain,
    ( spl4_36
  <=> ! [X0] :
        ( k3_xboole_0(k2_pre_topc(sK0,X0),sK2(sK0,sK1)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f336,plain,
    ( sK1 = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_18
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f335,f133])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f335,plain,
    ( sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK2(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f333,f93])).

fof(f333,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK2(sK0,sK1))
    | ~ spl4_18
    | ~ spl4_36 ),
    inference(resolution,[],[f301,f169])).

fof(f169,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k2_pre_topc(sK0,X0),sK2(sK0,sK1)) = X0 )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f300])).

fof(f320,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | spl4_28 ),
    inference(subsumption_resolution,[],[f318,f73])).

fof(f318,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | spl4_28 ),
    inference(subsumption_resolution,[],[f317,f93])).

fof(f317,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_6
    | spl4_28 ),
    inference(subsumption_resolution,[],[f316,f83])).

fof(f316,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_6
    | spl4_28 ),
    inference(subsumption_resolution,[],[f313,f88])).

fof(f313,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_28 ),
    inference(resolution,[],[f238,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f238,plain,
    ( ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl4_28
  <=> v2_tex_2(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f302,plain,
    ( spl4_36
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_28
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f297,f265,f237,f193,f177,f300])).

fof(f177,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f193,plain,
    ( spl4_21
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f265,plain,
    ( spl4_32
  <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1) = k3_xboole_0(X1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f297,plain,
    ( ! [X0] :
        ( k3_xboole_0(k2_pre_topc(sK0,X0),sK2(sK0,sK1)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1)) )
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_28
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f296,f266])).

fof(f266,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1) = k3_xboole_0(X1,sK2(sK0,sK1))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f265])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f197,f239])).

fof(f239,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f237])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK2(sK0,sK1),sK0)
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(resolution,[],[f195,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ r1_tarski(X0,X1)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f195,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f298,plain,
    ( spl4_33
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f271,f232,f276])).

fof(f232,plain,
    ( spl4_27
  <=> sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f271,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1))
    | ~ spl4_27 ),
    inference(superposition,[],[f54,f234])).

fof(f234,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f267,plain,
    ( spl4_32
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f258,f222,f193,f265])).

fof(f222,plain,
    ( spl4_25
  <=> ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2(sK0,sK1)) = k3_xboole_0(X2,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f258,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1) = k3_xboole_0(X1,sK2(sK0,sK1))
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f202,f223])).

fof(f223,plain,
    ( ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2(sK0,sK1)) = k3_xboole_0(X2,sK2(sK0,sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f222])).

% (10322)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f202,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1)
    | ~ spl4_21 ),
    inference(resolution,[],[f195,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f235,plain,
    ( spl4_27
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f214,f210,f232])).

fof(f210,plain,
    ( spl4_23
  <=> r1_tarski(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f214,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_23 ),
    inference(resolution,[],[f212,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f212,plain,
    ( r1_tarski(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f224,plain,
    ( spl4_25
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f203,f193,f222])).

fof(f203,plain,
    ( ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2(sK0,sK1)) = k3_xboole_0(X2,sK2(sK0,sK1))
    | ~ spl4_21 ),
    inference(resolution,[],[f195,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f213,plain,
    ( spl4_23
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f204,f193,f210])).

fof(f204,plain,
    ( r1_tarski(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_21 ),
    inference(resolution,[],[f195,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f196,plain,
    ( spl4_21
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f173,f163,f91,f86,f81,f193])).

fof(f163,plain,
    ( spl4_17
  <=> ! [X0] :
        ( m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f173,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f172,f88])).

fof(f172,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f171,f83])).

fof(f171,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(resolution,[],[f164,f93])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f163])).

fof(f179,plain,
    ( spl4_19
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f153,f71,f66,f61,f177])).

fof(f61,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f152,f63])).

fof(f63,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f151,f73])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f170,plain,
    ( spl4_18
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f161,f156,f91,f86,f81,f167])).

fof(f156,plain,
    ( spl4_16
  <=> ! [X0] :
        ( r1_tarski(X0,sK2(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f161,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f160,f88])).

fof(f160,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f159,f83])).

fof(f159,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f157,f93])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | r1_tarski(X0,sK2(sK0,X0))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f165,plain,
    ( spl4_17
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f135,f71,f163])).

fof(f135,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f44,f73])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f158,plain,
    ( spl4_16
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f120,f71,f156])).

fof(f120,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK2(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f46,f73])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f126,f122,f91,f76,f131])).

fof(f76,plain,
    ( spl4_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f122,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f126,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f125,f93])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(resolution,[],[f123,f78])).

fof(f78,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( spl4_12
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f114,f71,f122])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f48,f73])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f94,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f38,f91])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v3_tex_2(sK1,sK0)
    & v2_tex_2(sK1,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK0)
          & v2_tex_2(X1,sK0)
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ v3_tex_2(X1,sK0)
        & v2_tex_2(X1,sK0)
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tex_2(sK1,sK0)
      & v2_tex_2(sK1,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f89,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (10304)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (10305)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (10327)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (10308)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (10317)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (10319)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (10311)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (10309)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (10324)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (10307)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (10314)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (10304)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (10325)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (10320)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (10303)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (10316)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (10312)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (10315)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f471,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f124,f134,f158,f165,f170,f179,f196,f213,f224,f235,f267,f298,f302,f320,f342,f422,f470])).
% 0.20/0.52  fof(f470,plain,(
% 0.20/0.52    ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_44),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f469])).
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    $false | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_44)),
% 0.20/0.52    inference(subsumption_resolution,[],[f468,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    l1_pre_topc(sK0) | ~spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl4_3 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f468,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | (~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_44)),
% 0.20/0.52    inference(subsumption_resolution,[],[f467,f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f467,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_5 | spl4_6 | ~spl4_44)),
% 0.20/0.52    inference(subsumption_resolution,[],[f466,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    v2_tex_2(sK1,sK0) | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl4_5 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f466,plain,(
% 0.20/0.52    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_6 | ~spl4_44)),
% 0.20/0.52    inference(subsumption_resolution,[],[f464,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ~v3_tex_2(sK1,sK0) | spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    spl4_6 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f464,plain,(
% 0.20/0.52    v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_44),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f462])).
% 0.20/0.52  fof(f462,plain,(
% 0.20/0.52    sK1 != sK1 | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_44),
% 0.20/0.52    inference(superposition,[],[f47,f421])).
% 0.20/0.52  fof(f421,plain,(
% 0.20/0.52    sK1 = sK2(sK0,sK1) | ~spl4_44),
% 0.20/0.52    inference(avatar_component_clause,[],[f419])).
% 0.20/0.52  fof(f419,plain,(
% 0.20/0.52    spl4_44 <=> sK1 = sK2(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(rectify,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.52  fof(f422,plain,(
% 0.20/0.52    spl4_44 | ~spl4_33 | ~spl4_37),
% 0.20/0.52    inference(avatar_split_clause,[],[f390,f339,f276,f419])).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    spl4_33 <=> sK2(sK0,sK1) = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.52  fof(f339,plain,(
% 0.20/0.52    spl4_37 <=> sK1 = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.52  fof(f390,plain,(
% 0.20/0.52    sK1 = sK2(sK0,sK1) | (~spl4_33 | ~spl4_37)),
% 0.20/0.52    inference(forward_demodulation,[],[f278,f341])).
% 0.20/0.52  fof(f341,plain,(
% 0.20/0.52    sK1 = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1)) | ~spl4_37),
% 0.20/0.52    inference(avatar_component_clause,[],[f339])).
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1)) | ~spl4_33),
% 0.20/0.52    inference(avatar_component_clause,[],[f276])).
% 0.20/0.52  fof(f342,plain,(
% 0.20/0.52    spl4_37 | ~spl4_7 | ~spl4_13 | ~spl4_18 | ~spl4_36),
% 0.20/0.52    inference(avatar_split_clause,[],[f336,f300,f167,f131,f91,f339])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    spl4_13 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    spl4_18 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.52  fof(f300,plain,(
% 0.20/0.52    spl4_36 <=> ! [X0] : (k3_xboole_0(k2_pre_topc(sK0,X0),sK2(sK0,sK1)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    sK1 = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1)) | (~spl4_7 | ~spl4_13 | ~spl4_18 | ~spl4_36)),
% 0.20/0.52    inference(forward_demodulation,[],[f335,f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl4_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f131])).
% 0.20/0.52  fof(f335,plain,(
% 0.20/0.52    sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK2(sK0,sK1)) | (~spl4_7 | ~spl4_18 | ~spl4_36)),
% 0.20/0.52    inference(subsumption_resolution,[],[f333,f93])).
% 0.20/0.52  fof(f333,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK2(sK0,sK1)) | (~spl4_18 | ~spl4_36)),
% 0.20/0.52    inference(resolution,[],[f301,f169])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl4_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f167])).
% 0.20/0.52  fof(f301,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK2(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(k2_pre_topc(sK0,X0),sK2(sK0,sK1)) = X0) ) | ~spl4_36),
% 0.20/0.52    inference(avatar_component_clause,[],[f300])).
% 0.20/0.52  fof(f320,plain,(
% 0.20/0.52    ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_7 | spl4_28),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f319])).
% 0.20/0.52  fof(f319,plain,(
% 0.20/0.52    $false | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_7 | spl4_28)),
% 0.20/0.52    inference(subsumption_resolution,[],[f318,f73])).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | (~spl4_5 | spl4_6 | ~spl4_7 | spl4_28)),
% 0.20/0.52    inference(subsumption_resolution,[],[f317,f93])).
% 0.20/0.52  fof(f317,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_5 | spl4_6 | spl4_28)),
% 0.20/0.52    inference(subsumption_resolution,[],[f316,f83])).
% 0.20/0.52  fof(f316,plain,(
% 0.20/0.52    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_6 | spl4_28)),
% 0.20/0.52    inference(subsumption_resolution,[],[f313,f88])).
% 0.20/0.52  fof(f313,plain,(
% 0.20/0.52    v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_28),
% 0.20/0.52    inference(resolution,[],[f238,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ~v2_tex_2(sK2(sK0,sK1),sK0) | spl4_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f237])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    spl4_28 <=> v2_tex_2(sK2(sK0,sK1),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    spl4_36 | ~spl4_19 | ~spl4_21 | ~spl4_28 | ~spl4_32),
% 0.20/0.52    inference(avatar_split_clause,[],[f297,f265,f237,f193,f177,f300])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    spl4_19 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl4_21 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    spl4_32 <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1) = k3_xboole_0(X1,sK2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    ( ! [X0] : (k3_xboole_0(k2_pre_topc(sK0,X0),sK2(sK0,sK1)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1))) ) | (~spl4_19 | ~spl4_21 | ~spl4_28 | ~spl4_32)),
% 0.20/0.52    inference(forward_demodulation,[],[f296,f266])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1) = k3_xboole_0(X1,sK2(sK0,sK1))) ) | ~spl4_32),
% 0.20/0.52    inference(avatar_component_clause,[],[f265])).
% 0.20/0.52  fof(f296,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1)) | k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0) ) | (~spl4_19 | ~spl4_21 | ~spl4_28)),
% 0.20/0.52    inference(subsumption_resolution,[],[f197,f239])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~spl4_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f237])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK2(sK0,sK1),sK0) | ~r1_tarski(X0,sK2(sK0,sK1)) | k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0) ) | (~spl4_19 | ~spl4_21)),
% 0.20/0.52    inference(resolution,[],[f195,f178])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | ~spl4_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f177])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f193])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    spl4_33 | ~spl4_27),
% 0.20/0.52    inference(avatar_split_clause,[],[f271,f232,f276])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    spl4_27 <=> sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.52  fof(f271,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k3_xboole_0(u1_struct_0(sK0),sK2(sK0,sK1)) | ~spl4_27),
% 0.20/0.52    inference(superposition,[],[f54,f234])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f232])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    spl4_32 | ~spl4_21 | ~spl4_25),
% 0.20/0.52    inference(avatar_split_clause,[],[f258,f222,f193,f265])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    spl4_25 <=> ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2(sK0,sK1)) = k3_xboole_0(X2,sK2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.52  fof(f258,plain,(
% 0.20/0.52    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1) = k3_xboole_0(X1,sK2(sK0,sK1))) ) | (~spl4_21 | ~spl4_25)),
% 0.20/0.52    inference(forward_demodulation,[],[f202,f223])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,sK2(sK0,sK1)) = k3_xboole_0(X2,sK2(sK0,sK1))) ) | ~spl4_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f222])).
% 0.20/0.52  % (10322)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),X1)) ) | ~spl4_21),
% 0.20/0.52    inference(resolution,[],[f195,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    spl4_27 | ~spl4_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f214,f210,f232])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    spl4_23 <=> r1_tarski(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_23),
% 0.20/0.52    inference(resolution,[],[f212,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    r1_tarski(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f210])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    spl4_25 | ~spl4_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f203,f193,f222])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,sK2(sK0,sK1)) = k3_xboole_0(X2,sK2(sK0,sK1))) ) | ~spl4_21),
% 0.20/0.52    inference(resolution,[],[f195,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    spl4_23 | ~spl4_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f204,f193,f210])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    r1_tarski(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_21),
% 0.20/0.52    inference(resolution,[],[f195,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    spl4_21 | ~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f173,f163,f91,f86,f81,f193])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    spl4_17 <=> ! [X0] : (m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_17)),
% 0.20/0.52    inference(subsumption_resolution,[],[f172,f88])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (~spl4_5 | ~spl4_7 | ~spl4_17)),
% 0.20/0.52    inference(subsumption_resolution,[],[f171,f83])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    ~v2_tex_2(sK1,sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (~spl4_7 | ~spl4_17)),
% 0.20/0.52    inference(resolution,[],[f164,f93])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f163])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    spl4_19 | spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f153,f71,f66,f61,f177])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    spl4_1 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl4_2 <=> v2_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f152,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~v2_struct_0(sK0) | spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f61])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f151,f73])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f50,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    v2_pre_topc(sK0) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f66])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(rectify,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    spl4_18 | ~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f161,f156,f91,f86,f81,f167])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    spl4_16 <=> ! [X0] : (r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | (~spl4_5 | spl4_6 | ~spl4_7 | ~spl4_16)),
% 0.20/0.52    inference(subsumption_resolution,[],[f160,f88])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | (~spl4_5 | ~spl4_7 | ~spl4_16)),
% 0.20/0.52    inference(subsumption_resolution,[],[f159,f83])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ~v2_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | (~spl4_7 | ~spl4_16)),
% 0.20/0.52    inference(resolution,[],[f157,f93])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0)) | v3_tex_2(X0,sK0)) ) | ~spl4_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f156])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    spl4_17 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f135,f71,f163])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_3),
% 0.20/0.52    inference(resolution,[],[f44,f73])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl4_16 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f120,f71,f156])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_3),
% 0.20/0.52    inference(resolution,[],[f46,f73])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    spl4_13 | ~spl4_4 | ~spl4_7 | ~spl4_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f126,f122,f91,f76,f131])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl4_4 <=> v1_tops_1(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl4_12 <=> ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_7 | ~spl4_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f125,f93])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_12)),
% 0.20/0.52    inference(resolution,[],[f123,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    v1_tops_1(sK1,sK0) | ~spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f76])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl4_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f122])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl4_12 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f114,f71,f122])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl4_3),
% 0.20/0.52    inference(resolution,[],[f48,f73])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f91])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    (~v3_tex_2(sK1,sK0) & v2_tex_2(sK1,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK0) & v2_tex_2(X1,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X1] : (~v3_tex_2(X1,sK0) & v2_tex_2(X1,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v3_tex_2(sK1,sK0) & v2_tex_2(sK1,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f86])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ~v3_tex_2(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f81])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    v2_tex_2(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f76])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    v1_tops_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f71])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f66])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f61])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (10304)------------------------------
% 0.20/0.52  % (10304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10304)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (10304)Memory used [KB]: 6396
% 0.20/0.52  % (10304)Time elapsed: 0.098 s
% 0.20/0.52  % (10304)------------------------------
% 0.20/0.52  % (10304)------------------------------
% 0.20/0.52  % (10308)Refutation not found, incomplete strategy% (10308)------------------------------
% 0.20/0.52  % (10308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10298)Success in time 0.167 s
%------------------------------------------------------------------------------
