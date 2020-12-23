%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1851+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 119 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  173 ( 414 expanded)
%              Number of equality atoms :   52 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f50,f68,f80,f92,f103])).

fof(f103,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f101,f42,f34,f90])).

fof(f90,plain,
    ( spl2_11
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f34,plain,
    ( spl2_3
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f101,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f58,f35])).

fof(f35,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f58,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X3,X2)
        | u1_pre_topc(sK0) = X2 )
    | ~ spl2_5 ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = X2
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f24,f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (7325)Termination reason: Refutation not found, incomplete strategy

% (7325)Memory used [KB]: 10618
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

% (7325)Time elapsed: 0.110 s
% (7325)------------------------------
% (7325)------------------------------
fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f92,plain,
    ( ~ spl2_5
    | ~ spl2_2
    | ~ spl2_11
    | spl2_9 ),
    inference(avatar_split_clause,[],[f86,f78,f90,f30,f42])).

fof(f30,plain,
    ( spl2_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f78,plain,
    ( spl2_9
  <=> u1_pre_topc(sK1) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f86,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(superposition,[],[f79,f21])).

fof(f21,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f79,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( ~ spl2_9
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f73,f66,f48,f78])).

fof(f48,plain,
    ( spl2_6
  <=> u1_pre_topc(sK1) = k2_tarski(k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f66,plain,
    ( spl2_7
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f49,f67])).

fof(f67,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f49,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f68,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f64,f42,f34,f66])).

fof(f64,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f56,f35])).

fof(f56,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK0) = X2 )
    | ~ spl2_5 ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f23,f20])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f45,f26,f48,f38])).

fof(f38,plain,
    ( spl2_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f26,plain,
    ( spl2_1
  <=> v2_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | spl2_1 ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,
    ( ~ v2_tdlat_3(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f22,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ~ v2_tdlat_3(X1)
        & v2_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v2_tdlat_3(sK1)
      & v2_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
