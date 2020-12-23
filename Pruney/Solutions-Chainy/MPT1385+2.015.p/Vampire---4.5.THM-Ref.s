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
% DateTime   : Thu Dec  3 13:15:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 371 expanded)
%              Number of leaves         :   35 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  573 (1707 expanded)
%              Number of equality atoms :   25 (  84 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f92,f127,f129,f131,f141,f165,f176,f194,f205,f207,f225,f290,f449,f477,f507,f517,f523,f531])).

fof(f531,plain,
    ( spl3_2
    | ~ spl3_20
    | ~ spl3_16
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f529,f504,f203,f281,f88])).

fof(f88,plain,
    ( spl3_2
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f281,plain,
    ( spl3_20
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f203,plain,
    ( spl3_16
  <=> ! [X11] :
        ( ~ r2_hidden(X11,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | m1_connsp_2(sK2,sK0,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f504,plain,
    ( spl3_46
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f529,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_16
    | ~ spl3_46 ),
    inference(resolution,[],[f505,f204])).

fof(f204,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | m1_connsp_2(sK2,sK0,X11) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f203])).

fof(f505,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f504])).

fof(f523,plain,
    ( ~ spl3_20
    | spl3_46
    | ~ spl3_1
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f519,f447,f84,f504,f281])).

fof(f84,plain,
    ( spl3_1
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f447,plain,
    ( spl3_40
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f519,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_40 ),
    inference(resolution,[],[f85,f448])).

fof(f448,plain,
    ( ! [X3] :
        ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3))
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f447])).

fof(f85,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f517,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_2
    | spl3_46 ),
    inference(avatar_split_clause,[],[f515,f504,f88,f281,f121,f117,f147])).

fof(f147,plain,
    ( spl3_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f117,plain,
    ( spl3_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f121,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f515,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_46 ),
    inference(resolution,[],[f506,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_tops_1(X1,X0))
      | ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,k1_tops_1(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(condensation,[],[f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,k1_tops_1(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,k1_tops_1(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f506,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f504])).

fof(f507,plain,
    ( ~ spl3_20
    | ~ spl3_46
    | spl3_1
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f494,f475,f84,f504,f281])).

fof(f475,plain,
    ( spl3_43
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,k1_tops_1(sK0,sK2))
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f494,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_43 ),
    inference(resolution,[],[f476,f86])).

fof(f86,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f476,plain,
    ( ! [X4] :
        ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))
        | ~ r2_hidden(X4,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( spl3_10
    | spl3_43
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f472,f223,f475,f159])).

fof(f159,plain,
    ( spl3_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f223,plain,
    ( spl3_19
  <=> ! [X4] :
        ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f472,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))
        | ~ r2_hidden(X4,k1_tops_1(sK0,sK2))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f467])).

fof(f467,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))
        | ~ r2_hidden(X4,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_19 ),
    inference(resolution,[],[f224,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X2)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f80,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f224,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f223])).

fof(f449,plain,
    ( spl3_10
    | spl3_40
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f445,f163,f447,f159])).

fof(f163,plain,
    ( spl3_11
  <=> ! [X4] :
        ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f445,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3))
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_11 ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3))
        | r2_hidden(X3,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_11 ),
    inference(resolution,[],[f164,f98])).

fof(f98,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k6_domain_1(X4,X3),X5)
      | r2_hidden(X3,X5)
      | ~ m1_subset_1(X3,X4)
      | v1_xboole_0(X4) ) ),
    inference(superposition,[],[f82,f79])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f66,f77])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f164,plain,
    ( ! [X4] :
        ( r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f290,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl3_20 ),
    inference(resolution,[],[f283,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f283,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f281])).

fof(f225,plain,
    ( spl3_10
    | spl3_19
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f212,f139,f223,f159])).

fof(f139,plain,
    ( spl3_6
  <=> ! [X11] :
        ( ~ r1_tarski(X11,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(sK2,sK0,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f212,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2))
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f140,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X11,k1_tops_1(sK0,sK2))
        | m2_connsp_2(sK2,sK0,X11) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f207,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl3_15 ),
    inference(resolution,[],[f195,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f195,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_15 ),
    inference(resolution,[],[f193,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f193,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f205,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_4
    | spl3_16 ),
    inference(avatar_split_clause,[],[f199,f203,f121,f117,f147])).

fof(f199,plain,(
    ! [X11] :
      ( ~ r2_hidden(X11,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f194,plain,
    ( spl3_7
    | ~ spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f189,f159,f191,f147])).

fof(f189,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f161,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f161,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f176,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl3_7 ),
    inference(resolution,[],[f149,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f149,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f165,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f144,f125,f163,f159])).

fof(f125,plain,
    ( spl3_5
  <=> ! [X11] :
        ( ~ m2_connsp_2(sK2,sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X11,k1_tops_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f144,plain,
    ( ! [X4] :
        ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))
        | r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_5 ),
    inference(resolution,[],[f126,f62])).

fof(f126,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m2_connsp_2(sK2,sK0,X11)
        | r1_tarski(X11,k1_tops_1(sK0,sK2)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f141,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f135,f139,f121,f117])).

fof(f135,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f59,f50])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f131,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f123,f48])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f129,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f119,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f119,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f127,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f111,f125,f121,f117])).

fof(f111,plain,(
    ! [X11] :
      ( ~ m2_connsp_2(sK2,sK0,X11)
      | r1_tarski(X11,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f88,f84])).

fof(f51,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f88,f84])).

fof(f52,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (18528)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (18528)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f536,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f91,f92,f127,f129,f131,f141,f165,f176,f194,f205,f207,f225,f290,f449,f477,f507,f517,f523,f531])).
% 0.21/0.44  fof(f531,plain,(
% 0.21/0.44    spl3_2 | ~spl3_20 | ~spl3_16 | ~spl3_46),
% 0.21/0.44    inference(avatar_split_clause,[],[f529,f504,f203,f281,f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    spl3_2 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f281,plain,(
% 0.21/0.44    spl3_20 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f203,plain,(
% 0.21/0.44    spl3_16 <=> ! [X11] : (~r2_hidden(X11,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,X11))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.44  fof(f504,plain,(
% 0.21/0.44    spl3_46 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.44  fof(f529,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1) | (~spl3_16 | ~spl3_46)),
% 0.21/0.44    inference(resolution,[],[f505,f204])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    ( ! [X11] : (~r2_hidden(X11,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,X11)) ) | ~spl3_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f203])).
% 0.21/0.44  fof(f505,plain,(
% 0.21/0.44    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl3_46),
% 0.21/0.44    inference(avatar_component_clause,[],[f504])).
% 0.21/0.44  fof(f523,plain,(
% 0.21/0.44    ~spl3_20 | spl3_46 | ~spl3_1 | ~spl3_40),
% 0.21/0.44    inference(avatar_split_clause,[],[f519,f447,f84,f504,f281])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl3_1 <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f447,plain,(
% 0.21/0.44    spl3_40 <=> ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.44  fof(f519,plain,(
% 0.21/0.44    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_1 | ~spl3_40)),
% 0.21/0.44    inference(resolution,[],[f85,f448])).
% 0.21/0.44  fof(f448,plain,(
% 0.21/0.44    ( ! [X3] : (~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3)) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl3_40),
% 0.21/0.44    inference(avatar_component_clause,[],[f447])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f84])).
% 0.21/0.44  fof(f517,plain,(
% 0.21/0.44    spl3_7 | ~spl3_3 | ~spl3_4 | ~spl3_20 | ~spl3_2 | spl3_46),
% 0.21/0.44    inference(avatar_split_clause,[],[f515,f504,f88,f281,f121,f117,f147])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    spl3_7 <=> v2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl3_3 <=> v2_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f515,plain,(
% 0.21/0.44    ~m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl3_46),
% 0.21/0.44    inference(resolution,[],[f506,f184])).
% 0.21/0.44  fof(f184,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_tops_1(X1,X0)) | ~m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,X1,X2) | r2_hidden(X2,k1_tops_1(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.21/0.44    inference(condensation,[],[f182])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,X1,X2) | r2_hidden(X2,k1_tops_1(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_connsp_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f177])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,X1,X2) | r2_hidden(X2,k1_tops_1(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_connsp_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.44    inference(resolution,[],[f56,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.44  fof(f506,plain,(
% 0.21/0.44    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl3_46),
% 0.21/0.44    inference(avatar_component_clause,[],[f504])).
% 0.21/0.44  fof(f507,plain,(
% 0.21/0.44    ~spl3_20 | ~spl3_46 | spl3_1 | ~spl3_43),
% 0.21/0.44    inference(avatar_split_clause,[],[f494,f475,f84,f504,f281])).
% 0.21/0.44  fof(f475,plain,(
% 0.21/0.44    spl3_43 <=> ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.44  fof(f494,plain,(
% 0.21/0.44    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl3_1 | ~spl3_43)),
% 0.21/0.44    inference(resolution,[],[f476,f86])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f84])).
% 0.21/0.44  fof(f476,plain,(
% 0.21/0.44    ( ! [X4] : (m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) | ~r2_hidden(X4,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | ~spl3_43),
% 0.21/0.44    inference(avatar_component_clause,[],[f475])).
% 0.21/0.44  fof(f477,plain,(
% 0.21/0.44    spl3_10 | spl3_43 | ~spl3_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f472,f223,f475,f159])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    spl3_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    spl3_19 <=> ! [X4] : (~r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.44  fof(f472,plain,(
% 0.21/0.44    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) | ~r2_hidden(X4,k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_19),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f467])).
% 0.21/0.44  fof(f467,plain,(
% 0.21/0.44    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) | ~r2_hidden(X4,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_19),
% 0.21/0.44    inference(resolution,[],[f224,f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X2) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(superposition,[],[f80,f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f61,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f53,f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f60,f76])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f65,f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f69,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f70,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f71,f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f68,f77])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(flattening,[],[f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(nnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    ( ! [X4] : (~r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))) ) | ~spl3_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f223])).
% 0.21/0.44  fof(f449,plain,(
% 0.21/0.44    spl3_10 | spl3_40 | ~spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f445,f163,f447,f159])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    spl3_11 <=> ! [X4] : (~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f445,plain,(
% 0.21/0.44    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3)) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_11),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f440])).
% 0.21/0.44  fof(f440,plain,(
% 0.21/0.44    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X3)) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_11),
% 0.21/0.44    inference(resolution,[],[f164,f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ( ! [X4,X5,X3] : (~r1_tarski(k6_domain_1(X4,X3),X5) | r2_hidden(X3,X5) | ~m1_subset_1(X3,X4) | v1_xboole_0(X4)) )),
% 0.21/0.44    inference(superposition,[],[f82,f79])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f66,f77])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f45])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ( ! [X4] : (r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4))) ) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f163])).
% 0.21/0.44  fof(f290,plain,(
% 0.21/0.44    spl3_20),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f289])).
% 0.21/0.44  fof(f289,plain,(
% 0.21/0.44    $false | spl3_20),
% 0.21/0.44    inference(resolution,[],[f283,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f17])).
% 0.21/0.44  fof(f17,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.21/0.44  fof(f283,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f281])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    spl3_10 | spl3_19 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f212,f139,f223,f159])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    spl3_6 <=> ! [X11] : (~r1_tarski(X11,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(sK2,sK0,X11))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    ( ! [X4] : (~r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_6),
% 0.21/0.44    inference(resolution,[],[f140,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X11,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X11)) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f139])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    spl3_15),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.44  fof(f206,plain,(
% 0.21/0.44    $false | spl3_15),
% 0.21/0.44    inference(resolution,[],[f195,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | spl3_15),
% 0.21/0.44    inference(resolution,[],[f193,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f193,plain,(
% 0.21/0.44    ~l1_struct_0(sK0) | spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f191])).
% 0.21/0.44  fof(f191,plain,(
% 0.21/0.44    spl3_15 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f205,plain,(
% 0.21/0.44    spl3_7 | ~spl3_3 | ~spl3_4 | spl3_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f199,f203,f121,f117,f147])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    ( ! [X11] : (~r2_hidden(X11,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X11) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f57,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f194,plain,(
% 0.21/0.44    spl3_7 | ~spl3_15 | ~spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f189,f159,f191,f147])).
% 0.21/0.44  fof(f189,plain,(
% 0.21/0.44    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.21/0.44    inference(resolution,[],[f161,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f159])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    ~spl3_7),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    $false | ~spl3_7),
% 0.21/0.44    inference(resolution,[],[f149,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    v2_struct_0(sK0) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f147])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    spl3_10 | spl3_11 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f144,f125,f163,f159])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    spl3_5 <=> ! [X11] : (~m2_connsp_2(sK2,sK0,X11) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X11,k1_tops_1(sK0,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    ( ! [X4] : (~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X4)) | r1_tarski(k6_domain_1(u1_struct_0(sK0),X4),k1_tops_1(sK0,sK2)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_5),
% 0.21/0.44    inference(resolution,[],[f126,f62])).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_connsp_2(sK2,sK0,X11) | r1_tarski(X11,k1_tops_1(sK0,sK2))) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f125])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    ~spl3_3 | ~spl3_4 | spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f135,f139,f121,f117])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    ( ! [X11] : (~r1_tarski(X11,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X11) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f59,f50])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    $false | spl3_4),
% 0.21/0.44    inference(resolution,[],[f123,f48])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f121])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.44  fof(f128,plain,(
% 0.21/0.44    $false | spl3_3),
% 0.21/0.44    inference(resolution,[],[f119,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    ~v2_pre_topc(sK0) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f117])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    ~spl3_3 | ~spl3_4 | spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f111,f125,f121,f117])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X11] : (~m2_connsp_2(sK2,sK0,X11) | r1_tarski(X11,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f58,f50])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl3_1 | spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f51,f88,f84])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ~spl3_1 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f52,f88,f84])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (18528)------------------------------
% 0.21/0.44  % (18528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (18528)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (18528)Memory used [KB]: 6396
% 0.21/0.44  % (18528)Time elapsed: 0.016 s
% 0.21/0.44  % (18528)------------------------------
% 0.21/0.44  % (18528)------------------------------
% 0.21/0.45  % (18523)Success in time 0.088 s
%------------------------------------------------------------------------------
