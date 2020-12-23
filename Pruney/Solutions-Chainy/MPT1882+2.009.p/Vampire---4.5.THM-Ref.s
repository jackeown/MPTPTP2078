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
% DateTime   : Thu Dec  3 13:22:00 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 557 expanded)
%              Number of leaves         :   25 ( 160 expanded)
%              Depth                    :   18
%              Number of atoms          :  597 (3795 expanded)
%              Number of equality atoms :   56 ( 182 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f284,f300,f309,f399,f525,f567,f754])).

fof(f754,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f753])).

fof(f753,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f752,f173])).

fof(f173,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_3
  <=> v2_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f752,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f751,f127])).

fof(f127,plain,
    ( ~ sP0(sK3,sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f125,f84])).

fof(f84,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> v3_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f125,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f124,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f124,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v3_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK2) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK3)
        | ~ v3_tex_2(sK3,sK2) )
      & ( v1_zfmisc_1(sK3)
        | v3_tex_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f123,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f751,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f736,f187])).

fof(f187,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f73,f162])).

fof(f162,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f152,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f74,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f152,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f78,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f76,f69])).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f736,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f134,f634])).

fof(f634,plain,
    ( k1_xboole_0 = sK4(sK3,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f390,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f390,plain,
    ( v1_xboole_0(sK4(sK3,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl5_6
  <=> v1_xboole_0(sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f130,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK4(X0,X1))
      | ~ r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(extensionality_resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f567,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f565,f173])).

fof(f565,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f564,f127])).

fof(f564,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f550,f79])).

fof(f550,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl5_8 ),
    inference(superposition,[],[f134,f398])).

fof(f398,plain,
    ( sK3 = sK4(sK3,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl5_8
  <=> sK3 = sK4(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f525,plain,
    ( spl5_1
    | ~ spl5_3
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f523,f173])).

fof(f523,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl5_1
    | spl5_7 ),
    inference(subsumption_resolution,[],[f522,f127])).

fof(f522,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f521,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f521,plain,
    ( v2_struct_0(sK2)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f520,f47])).

fof(f47,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f520,plain,
    ( ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f517,f48])).

fof(f517,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl5_7 ),
    inference(resolution,[],[f200,f394])).

fof(f394,plain,
    ( ~ v1_zfmisc_1(sK4(sK3,sK2))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl5_7
  <=> v1_zfmisc_1(sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f200,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(sK4(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f199,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(sK4(X0,X1),X1)
      | v1_zfmisc_1(sK4(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(resolution,[],[f195,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f194,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f194,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f66,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f399,plain,
    ( spl5_6
    | ~ spl5_7
    | spl5_8
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f386,f172,f82,f396,f392,f388])).

fof(f386,plain,
    ( sK3 = sK4(sK3,sK2)
    | ~ v1_zfmisc_1(sK4(sK3,sK2))
    | v1_xboole_0(sK4(sK3,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f383,f49])).

fof(f49,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f383,plain,
    ( sK3 = sK4(sK3,sK2)
    | ~ v1_zfmisc_1(sK4(sK3,sK2))
    | v1_xboole_0(sK4(sK3,sK2))
    | v1_xboole_0(sK3)
    | spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f379,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f379,plain,
    ( r1_tarski(sK3,sK4(sK3,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f371])).

fof(f371,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,sK4(sK3,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(superposition,[],[f73,f357])).

fof(f357,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f356,f127])).

fof(f356,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f129,f173])).

fof(f129,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,X3)
      | sP0(X2,X3)
      | k1_xboole_0 = k4_xboole_0(X2,sK4(X2,X3)) ) ),
    inference(resolution,[],[f62,f74])).

fof(f309,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f308,f86,f172])).

fof(f86,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f308,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f307,f45])).

fof(f307,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f306,f47])).

fof(f306,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f305,f48])).

fof(f305,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f271,f49])).

fof(f271,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f239,f50])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f300,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f292,f298])).

fof(f298,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f297,f45])).

fof(f297,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f296,f47])).

fof(f296,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f295,f48])).

fof(f295,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f198,f88])).

fof(f88,plain,
    ( ~ v1_zfmisc_1(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f198,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f195,f50])).

fof(f292,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f283,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f283,plain,
    ( sP0(sK3,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl5_5
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f284,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f126,f82,f281])).

fof(f126,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f51,f86,f82])).

fof(f51,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f86,f82])).

fof(f52,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:19:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (3680)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (3681)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.56  % (3672)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.56  % (3673)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.56  % (3664)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (3665)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.54/0.57  % (3658)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.54/0.57  % (3662)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.54/0.57  % (3659)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.54/0.58  % (3661)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.54/0.58  % (3685)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.54/0.58  % (3668)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.54/0.58  % (3674)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.58  % (3667)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.54/0.58  % (3686)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.54/0.58  % (3677)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.58  % (3659)Refutation not found, incomplete strategy% (3659)------------------------------
% 1.54/0.58  % (3659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (3659)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (3659)Memory used [KB]: 1791
% 1.54/0.58  % (3659)Time elapsed: 0.154 s
% 1.54/0.58  % (3659)------------------------------
% 1.54/0.58  % (3659)------------------------------
% 1.54/0.58  % (3676)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.54/0.59  % (3669)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.54/0.59  % (3682)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.54/0.59  % (3678)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.59  % (3671)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.54/0.59  % (3679)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.54/0.59  % (3685)Refutation not found, incomplete strategy% (3685)------------------------------
% 1.54/0.59  % (3685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (3687)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.54/0.59  % (3668)Refutation not found, incomplete strategy% (3668)------------------------------
% 1.54/0.59  % (3668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (3668)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.59  
% 1.54/0.59  % (3668)Memory used [KB]: 10746
% 1.54/0.59  % (3668)Time elapsed: 0.160 s
% 1.54/0.59  % (3668)------------------------------
% 1.54/0.59  % (3668)------------------------------
% 1.54/0.59  % (3660)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.54/0.59  % (3675)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.54/0.59  % (3684)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.54/0.59  % (3663)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.54/0.59  % (3666)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.54/0.59  % (3683)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.54/0.59  % (3670)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.59  % (3687)Refutation not found, incomplete strategy% (3687)------------------------------
% 1.54/0.59  % (3687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (3664)Refutation found. Thanks to Tanya!
% 1.54/0.59  % SZS status Theorem for theBenchmark
% 1.54/0.60  % (3685)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.60  
% 1.54/0.60  % (3685)Memory used [KB]: 6268
% 1.54/0.60  % (3685)Time elapsed: 0.169 s
% 1.54/0.60  % (3685)------------------------------
% 1.54/0.60  % (3685)------------------------------
% 1.54/0.60  % (3674)Refutation not found, incomplete strategy% (3674)------------------------------
% 1.54/0.60  % (3674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (3674)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.60  
% 1.54/0.60  % (3674)Memory used [KB]: 10746
% 1.54/0.60  % (3674)Time elapsed: 0.177 s
% 1.54/0.60  % (3674)------------------------------
% 1.54/0.60  % (3674)------------------------------
% 1.54/0.60  % (3686)Refutation not found, incomplete strategy% (3686)------------------------------
% 1.54/0.60  % (3686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (3686)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.60  
% 1.54/0.60  % (3686)Memory used [KB]: 10746
% 1.54/0.60  % (3686)Time elapsed: 0.179 s
% 1.54/0.60  % (3686)------------------------------
% 1.54/0.60  % (3686)------------------------------
% 1.54/0.61  % (3687)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.61  
% 1.54/0.61  % (3687)Memory used [KB]: 1791
% 1.54/0.61  % (3687)Time elapsed: 0.122 s
% 1.54/0.61  % (3687)------------------------------
% 1.54/0.61  % (3687)------------------------------
% 1.54/0.61  % SZS output start Proof for theBenchmark
% 1.54/0.61  fof(f758,plain,(
% 1.54/0.61    $false),
% 1.54/0.61    inference(avatar_sat_refutation,[],[f89,f90,f284,f300,f309,f399,f525,f567,f754])).
% 1.54/0.61  fof(f754,plain,(
% 1.54/0.61    spl5_1 | ~spl5_3 | ~spl5_6),
% 1.54/0.61    inference(avatar_contradiction_clause,[],[f753])).
% 1.54/0.61  fof(f753,plain,(
% 1.54/0.61    $false | (spl5_1 | ~spl5_3 | ~spl5_6)),
% 1.54/0.61    inference(subsumption_resolution,[],[f752,f173])).
% 1.54/0.61  fof(f173,plain,(
% 1.54/0.61    v2_tex_2(sK3,sK2) | ~spl5_3),
% 1.54/0.61    inference(avatar_component_clause,[],[f172])).
% 1.54/0.61  fof(f172,plain,(
% 1.54/0.61    spl5_3 <=> v2_tex_2(sK3,sK2)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.54/0.61  fof(f752,plain,(
% 1.54/0.61    ~v2_tex_2(sK3,sK2) | (spl5_1 | ~spl5_6)),
% 1.54/0.61    inference(subsumption_resolution,[],[f751,f127])).
% 1.54/0.61  fof(f127,plain,(
% 1.54/0.61    ~sP0(sK3,sK2) | spl5_1),
% 1.54/0.61    inference(subsumption_resolution,[],[f125,f84])).
% 1.54/0.61  fof(f84,plain,(
% 1.54/0.61    ~v3_tex_2(sK3,sK2) | spl5_1),
% 1.54/0.61    inference(avatar_component_clause,[],[f82])).
% 1.54/0.61  fof(f82,plain,(
% 1.54/0.61    spl5_1 <=> v3_tex_2(sK3,sK2)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.54/0.61  fof(f125,plain,(
% 1.54/0.61    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 1.54/0.61    inference(resolution,[],[f124,f57])).
% 1.54/0.61  fof(f57,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f35])).
% 1.54/0.61  fof(f35,plain,(
% 1.54/0.61    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.54/0.61    inference(nnf_transformation,[],[f28])).
% 1.54/0.61  fof(f28,plain,(
% 1.54/0.61    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.54/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.54/0.61  fof(f124,plain,(
% 1.54/0.61    sP1(sK2,sK3)),
% 1.54/0.61    inference(subsumption_resolution,[],[f123,f48])).
% 1.54/0.61  fof(f48,plain,(
% 1.54/0.61    l1_pre_topc(sK2)),
% 1.54/0.61    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f34,plain,(
% 1.54/0.62    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.54/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).
% 1.54/0.62  fof(f32,plain,(
% 1.54/0.62    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.54/0.62    introduced(choice_axiom,[])).
% 1.54/0.62  fof(f33,plain,(
% 1.54/0.62    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3))),
% 1.54/0.62    introduced(choice_axiom,[])).
% 1.54/0.62  fof(f31,plain,(
% 1.54/0.62    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.62    inference(flattening,[],[f30])).
% 1.54/0.62  fof(f30,plain,(
% 1.54/0.62    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.62    inference(nnf_transformation,[],[f16])).
% 1.54/0.62  fof(f16,plain,(
% 1.54/0.62    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.62    inference(flattening,[],[f15])).
% 1.54/0.62  fof(f15,plain,(
% 1.54/0.62    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.54/0.62    inference(ennf_transformation,[],[f14])).
% 1.54/0.62  fof(f14,negated_conjecture,(
% 1.54/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.54/0.62    inference(negated_conjecture,[],[f13])).
% 1.54/0.62  fof(f13,conjecture,(
% 1.54/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 1.54/0.62  fof(f123,plain,(
% 1.54/0.62    sP1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.54/0.62    inference(resolution,[],[f64,f50])).
% 1.54/0.62  fof(f50,plain,(
% 1.54/0.62    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f64,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f29])).
% 1.54/0.62  fof(f29,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.62    inference(definition_folding,[],[f22,f28,f27])).
% 1.54/0.62  fof(f27,plain,(
% 1.54/0.62    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 1.54/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.62  fof(f22,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.62    inference(flattening,[],[f21])).
% 1.54/0.62  fof(f21,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.62    inference(ennf_transformation,[],[f10])).
% 1.54/0.62  fof(f10,axiom,(
% 1.54/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.54/0.62  fof(f751,plain,(
% 1.54/0.62    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl5_6),
% 1.54/0.62    inference(subsumption_resolution,[],[f736,f187])).
% 1.54/0.62  fof(f187,plain,(
% 1.54/0.62    ( ! [X5] : (r1_tarski(k1_xboole_0,X5)) )),
% 1.54/0.62    inference(trivial_inequality_removal,[],[f185])).
% 1.54/0.62  fof(f185,plain,(
% 1.54/0.62    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X5)) )),
% 1.54/0.62    inference(superposition,[],[f73,f162])).
% 1.54/0.62  fof(f162,plain,(
% 1.54/0.62    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.54/0.62    inference(forward_demodulation,[],[f152,f99])).
% 1.54/0.62  fof(f99,plain,(
% 1.54/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.54/0.62    inference(resolution,[],[f74,f79])).
% 1.54/0.62  fof(f79,plain,(
% 1.54/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.62    inference(equality_resolution,[],[f71])).
% 1.54/0.62  fof(f71,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.62    inference(cnf_transformation,[],[f43])).
% 1.54/0.62  fof(f43,plain,(
% 1.54/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.62    inference(flattening,[],[f42])).
% 1.54/0.62  fof(f42,plain,(
% 1.54/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.62    inference(nnf_transformation,[],[f2])).
% 1.54/0.62  fof(f2,axiom,(
% 1.54/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.62  fof(f74,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f44])).
% 1.54/0.62  fof(f44,plain,(
% 1.54/0.62    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.54/0.62    inference(nnf_transformation,[],[f3])).
% 1.54/0.62  fof(f3,axiom,(
% 1.54/0.62    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.62  fof(f152,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 1.54/0.62    inference(superposition,[],[f78,f77])).
% 1.54/0.62  fof(f77,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.54/0.62    inference(definition_unfolding,[],[f68,f69])).
% 1.54/0.62  fof(f69,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f7])).
% 1.54/0.62  fof(f7,axiom,(
% 1.54/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.54/0.62  fof(f68,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f5])).
% 1.54/0.62  fof(f5,axiom,(
% 1.54/0.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.54/0.62  fof(f78,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.54/0.62    inference(definition_unfolding,[],[f76,f69])).
% 1.54/0.62  fof(f76,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f4])).
% 1.54/0.62  fof(f4,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.54/0.62  fof(f73,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f44])).
% 1.54/0.62  fof(f736,plain,(
% 1.54/0.62    ~r1_tarski(k1_xboole_0,sK3) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl5_6),
% 1.54/0.62    inference(superposition,[],[f134,f634])).
% 1.54/0.62  fof(f634,plain,(
% 1.54/0.62    k1_xboole_0 = sK4(sK3,sK2) | ~spl5_6),
% 1.54/0.62    inference(resolution,[],[f390,f93])).
% 1.54/0.62  fof(f93,plain,(
% 1.54/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.54/0.62    inference(resolution,[],[f75,f53])).
% 1.54/0.62  fof(f53,plain,(
% 1.54/0.62    v1_xboole_0(k1_xboole_0)),
% 1.54/0.62    inference(cnf_transformation,[],[f1])).
% 1.54/0.62  fof(f1,axiom,(
% 1.54/0.62    v1_xboole_0(k1_xboole_0)),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.54/0.62  fof(f75,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f26])).
% 1.54/0.62  fof(f26,plain,(
% 1.54/0.62    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.54/0.62    inference(ennf_transformation,[],[f6])).
% 1.54/0.62  fof(f6,axiom,(
% 1.54/0.62    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.54/0.62  fof(f390,plain,(
% 1.54/0.62    v1_xboole_0(sK4(sK3,sK2)) | ~spl5_6),
% 1.54/0.62    inference(avatar_component_clause,[],[f388])).
% 1.54/0.62  fof(f388,plain,(
% 1.54/0.62    spl5_6 <=> v1_xboole_0(sK4(sK3,sK2))),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.54/0.62  fof(f134,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(subsumption_resolution,[],[f130,f62])).
% 1.54/0.62  fof(f62,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f40])).
% 1.54/0.62  fof(f40,plain,(
% 1.54/0.62    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.54/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.54/0.62  fof(f39,plain,(
% 1.54/0.62    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.54/0.62    introduced(choice_axiom,[])).
% 1.54/0.62  fof(f38,plain,(
% 1.54/0.62    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.54/0.62    inference(rectify,[],[f37])).
% 1.54/0.62  fof(f37,plain,(
% 1.54/0.62    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.54/0.62    inference(flattening,[],[f36])).
% 1.54/0.62  fof(f36,plain,(
% 1.54/0.62    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.54/0.62    inference(nnf_transformation,[],[f27])).
% 1.54/0.62  fof(f130,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X0,sK4(X0,X1)) | ~r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(extensionality_resolution,[],[f72,f63])).
% 1.54/0.62  fof(f63,plain,(
% 1.54/0.62    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f40])).
% 1.54/0.62  fof(f72,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f43])).
% 1.54/0.62  fof(f567,plain,(
% 1.54/0.62    spl5_1 | ~spl5_3 | ~spl5_8),
% 1.54/0.62    inference(avatar_contradiction_clause,[],[f566])).
% 1.54/0.62  fof(f566,plain,(
% 1.54/0.62    $false | (spl5_1 | ~spl5_3 | ~spl5_8)),
% 1.54/0.62    inference(subsumption_resolution,[],[f565,f173])).
% 1.54/0.62  fof(f565,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | (spl5_1 | ~spl5_8)),
% 1.54/0.62    inference(subsumption_resolution,[],[f564,f127])).
% 1.54/0.62  fof(f564,plain,(
% 1.54/0.62    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl5_8),
% 1.54/0.62    inference(subsumption_resolution,[],[f550,f79])).
% 1.54/0.62  fof(f550,plain,(
% 1.54/0.62    ~r1_tarski(sK3,sK3) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl5_8),
% 1.54/0.62    inference(superposition,[],[f134,f398])).
% 1.54/0.62  fof(f398,plain,(
% 1.54/0.62    sK3 = sK4(sK3,sK2) | ~spl5_8),
% 1.54/0.62    inference(avatar_component_clause,[],[f396])).
% 1.54/0.62  fof(f396,plain,(
% 1.54/0.62    spl5_8 <=> sK3 = sK4(sK3,sK2)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.54/0.62  fof(f525,plain,(
% 1.54/0.62    spl5_1 | ~spl5_3 | spl5_7),
% 1.54/0.62    inference(avatar_contradiction_clause,[],[f524])).
% 1.54/0.62  fof(f524,plain,(
% 1.54/0.62    $false | (spl5_1 | ~spl5_3 | spl5_7)),
% 1.54/0.62    inference(subsumption_resolution,[],[f523,f173])).
% 1.54/0.62  fof(f523,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | (spl5_1 | spl5_7)),
% 1.54/0.62    inference(subsumption_resolution,[],[f522,f127])).
% 1.54/0.62  fof(f522,plain,(
% 1.54/0.62    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | spl5_7),
% 1.54/0.62    inference(subsumption_resolution,[],[f521,f45])).
% 1.54/0.62  fof(f45,plain,(
% 1.54/0.62    ~v2_struct_0(sK2)),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f521,plain,(
% 1.54/0.62    v2_struct_0(sK2) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | spl5_7),
% 1.54/0.62    inference(subsumption_resolution,[],[f520,f47])).
% 1.54/0.62  fof(f47,plain,(
% 1.54/0.62    v2_tdlat_3(sK2)),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f520,plain,(
% 1.54/0.62    ~v2_tdlat_3(sK2) | v2_struct_0(sK2) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | spl5_7),
% 1.54/0.62    inference(subsumption_resolution,[],[f517,f48])).
% 1.54/0.62  fof(f517,plain,(
% 1.54/0.62    ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | spl5_7),
% 1.54/0.62    inference(resolution,[],[f200,f394])).
% 1.54/0.62  fof(f394,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK4(sK3,sK2)) | spl5_7),
% 1.54/0.62    inference(avatar_component_clause,[],[f392])).
% 1.54/0.62  fof(f392,plain,(
% 1.54/0.62    spl5_7 <=> v1_zfmisc_1(sK4(sK3,sK2))),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.54/0.62  fof(f200,plain,(
% 1.54/0.62    ( ! [X0,X1] : (v1_zfmisc_1(sK4(X0,X1)) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | v2_struct_0(X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(subsumption_resolution,[],[f199,f61])).
% 1.54/0.62  fof(f61,plain,(
% 1.54/0.62    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f40])).
% 1.54/0.62  fof(f199,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~v2_tex_2(sK4(X0,X1),X1) | v1_zfmisc_1(sK4(X0,X1)) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | v2_struct_0(X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(resolution,[],[f195,f60])).
% 1.54/0.62  fof(f60,plain,(
% 1.54/0.62    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f40])).
% 1.54/0.62  fof(f195,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.54/0.62    inference(subsumption_resolution,[],[f194,f65])).
% 1.54/0.62  fof(f65,plain,(
% 1.54/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f23])).
% 1.54/0.62  fof(f23,plain,(
% 1.54/0.62    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.54/0.62    inference(ennf_transformation,[],[f8])).
% 1.54/0.62  fof(f8,axiom,(
% 1.54/0.62    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.54/0.62  fof(f194,plain,(
% 1.54/0.62    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.54/0.62    inference(subsumption_resolution,[],[f66,f55])).
% 1.54/0.62  fof(f55,plain,(
% 1.54/0.62    ( ! [X0] : (~v2_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f20])).
% 1.54/0.62  fof(f20,plain,(
% 1.54/0.62    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.54/0.62    inference(flattening,[],[f19])).
% 1.54/0.62  fof(f19,plain,(
% 1.54/0.62    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.54/0.62    inference(ennf_transformation,[],[f9])).
% 1.54/0.62  fof(f9,axiom,(
% 1.54/0.62    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.54/0.62  fof(f66,plain,(
% 1.54/0.62    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f41])).
% 1.54/0.62  fof(f41,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.62    inference(nnf_transformation,[],[f25])).
% 1.54/0.62  fof(f25,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.62    inference(flattening,[],[f24])).
% 1.54/0.62  fof(f24,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.62    inference(ennf_transformation,[],[f12])).
% 1.54/0.62  fof(f12,axiom,(
% 1.54/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.54/0.62  fof(f399,plain,(
% 1.54/0.62    spl5_6 | ~spl5_7 | spl5_8 | spl5_1 | ~spl5_3),
% 1.54/0.62    inference(avatar_split_clause,[],[f386,f172,f82,f396,f392,f388])).
% 1.54/0.62  fof(f386,plain,(
% 1.54/0.62    sK3 = sK4(sK3,sK2) | ~v1_zfmisc_1(sK4(sK3,sK2)) | v1_xboole_0(sK4(sK3,sK2)) | (spl5_1 | ~spl5_3)),
% 1.54/0.62    inference(subsumption_resolution,[],[f383,f49])).
% 1.54/0.62  fof(f49,plain,(
% 1.54/0.62    ~v1_xboole_0(sK3)),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f383,plain,(
% 1.54/0.62    sK3 = sK4(sK3,sK2) | ~v1_zfmisc_1(sK4(sK3,sK2)) | v1_xboole_0(sK4(sK3,sK2)) | v1_xboole_0(sK3) | (spl5_1 | ~spl5_3)),
% 1.54/0.62    inference(resolution,[],[f379,f54])).
% 1.54/0.62  fof(f54,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f18])).
% 1.54/0.62  fof(f18,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.54/0.62    inference(flattening,[],[f17])).
% 1.54/0.62  fof(f17,plain,(
% 1.54/0.62    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.54/0.62    inference(ennf_transformation,[],[f11])).
% 1.54/0.62  fof(f11,axiom,(
% 1.54/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.54/0.62  fof(f379,plain,(
% 1.54/0.62    r1_tarski(sK3,sK4(sK3,sK2)) | (spl5_1 | ~spl5_3)),
% 1.54/0.62    inference(trivial_inequality_removal,[],[f371])).
% 1.54/0.62  fof(f371,plain,(
% 1.54/0.62    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK3,sK4(sK3,sK2)) | (spl5_1 | ~spl5_3)),
% 1.54/0.62    inference(superposition,[],[f73,f357])).
% 1.54/0.62  fof(f357,plain,(
% 1.54/0.62    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) | (spl5_1 | ~spl5_3)),
% 1.54/0.62    inference(subsumption_resolution,[],[f356,f127])).
% 1.54/0.62  fof(f356,plain,(
% 1.54/0.62    sP0(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) | ~spl5_3),
% 1.54/0.62    inference(resolution,[],[f129,f173])).
% 1.54/0.62  fof(f129,plain,(
% 1.54/0.62    ( ! [X2,X3] : (~v2_tex_2(X2,X3) | sP0(X2,X3) | k1_xboole_0 = k4_xboole_0(X2,sK4(X2,X3))) )),
% 1.54/0.62    inference(resolution,[],[f62,f74])).
% 1.54/0.62  fof(f309,plain,(
% 1.54/0.62    spl5_3 | ~spl5_2),
% 1.54/0.62    inference(avatar_split_clause,[],[f308,f86,f172])).
% 1.54/0.62  fof(f86,plain,(
% 1.54/0.62    spl5_2 <=> v1_zfmisc_1(sK3)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.54/0.62  fof(f308,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 1.54/0.62    inference(subsumption_resolution,[],[f307,f45])).
% 1.54/0.62  fof(f307,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | v2_struct_0(sK2)),
% 1.54/0.62    inference(subsumption_resolution,[],[f306,f47])).
% 1.54/0.62  fof(f306,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.54/0.62    inference(subsumption_resolution,[],[f305,f48])).
% 1.54/0.62  fof(f305,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.54/0.62    inference(subsumption_resolution,[],[f271,f49])).
% 1.54/0.62  fof(f271,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | v1_xboole_0(sK3) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.54/0.62    inference(resolution,[],[f239,f50])).
% 1.54/0.62  fof(f239,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.54/0.62    inference(subsumption_resolution,[],[f67,f55])).
% 1.54/0.62  fof(f67,plain,(
% 1.54/0.62    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f41])).
% 1.54/0.62  fof(f300,plain,(
% 1.54/0.62    spl5_2 | ~spl5_5),
% 1.54/0.62    inference(avatar_contradiction_clause,[],[f299])).
% 1.54/0.62  fof(f299,plain,(
% 1.54/0.62    $false | (spl5_2 | ~spl5_5)),
% 1.54/0.62    inference(subsumption_resolution,[],[f292,f298])).
% 1.54/0.62  fof(f298,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | spl5_2),
% 1.54/0.62    inference(subsumption_resolution,[],[f297,f45])).
% 1.54/0.62  fof(f297,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | v2_struct_0(sK2) | spl5_2),
% 1.54/0.62    inference(subsumption_resolution,[],[f296,f47])).
% 1.54/0.62  fof(f296,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2) | spl5_2),
% 1.54/0.62    inference(subsumption_resolution,[],[f295,f48])).
% 1.54/0.62  fof(f295,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2) | spl5_2),
% 1.54/0.62    inference(subsumption_resolution,[],[f198,f88])).
% 1.54/0.62  fof(f88,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | spl5_2),
% 1.54/0.62    inference(avatar_component_clause,[],[f86])).
% 1.54/0.62  fof(f198,plain,(
% 1.54/0.62    ~v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.54/0.62    inference(resolution,[],[f195,f50])).
% 1.54/0.62  fof(f292,plain,(
% 1.54/0.62    v2_tex_2(sK3,sK2) | ~spl5_5),
% 1.54/0.62    inference(resolution,[],[f283,f58])).
% 1.54/0.62  fof(f58,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~sP0(X0,X1) | v2_tex_2(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f40])).
% 1.54/0.62  fof(f283,plain,(
% 1.54/0.62    sP0(sK3,sK2) | ~spl5_5),
% 1.54/0.62    inference(avatar_component_clause,[],[f281])).
% 1.54/0.62  fof(f281,plain,(
% 1.54/0.62    spl5_5 <=> sP0(sK3,sK2)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.54/0.62  fof(f284,plain,(
% 1.54/0.62    spl5_5 | ~spl5_1),
% 1.54/0.62    inference(avatar_split_clause,[],[f126,f82,f281])).
% 1.54/0.62  fof(f126,plain,(
% 1.54/0.62    ~v3_tex_2(sK3,sK2) | sP0(sK3,sK2)),
% 1.54/0.62    inference(resolution,[],[f124,f56])).
% 1.54/0.62  fof(f56,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f35])).
% 1.54/0.62  fof(f90,plain,(
% 1.54/0.62    spl5_1 | spl5_2),
% 1.54/0.62    inference(avatar_split_clause,[],[f51,f86,f82])).
% 1.54/0.62  fof(f51,plain,(
% 1.54/0.62    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f89,plain,(
% 1.54/0.62    ~spl5_1 | ~spl5_2),
% 1.54/0.62    inference(avatar_split_clause,[],[f52,f86,f82])).
% 1.54/0.62  fof(f52,plain,(
% 1.54/0.62    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  % SZS output end Proof for theBenchmark
% 1.54/0.62  % (3664)------------------------------
% 1.54/0.62  % (3664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.62  % (3664)Termination reason: Refutation
% 1.54/0.62  
% 1.54/0.62  % (3664)Memory used [KB]: 11257
% 1.54/0.62  % (3664)Time elapsed: 0.162 s
% 1.54/0.62  % (3664)------------------------------
% 1.54/0.62  % (3664)------------------------------
% 1.54/0.62  % (3657)Success in time 0.244 s
%------------------------------------------------------------------------------
