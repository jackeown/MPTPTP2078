%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1314+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 247 expanded)
%              Number of leaves         :   33 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 (1009 expanded)
%              Number of equality atoms :   59 ( 171 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f78,f82,f87,f99,f104,f114,f127,f134,f140,f392,f402,f412,f438])).

fof(f438,plain,
    ( ~ spl5_16
    | spl5_8
    | ~ spl5_15
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f436,f400,f129,f85,f136])).

fof(f136,plain,
    ( spl5_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f85,plain,
    ( spl5_8
  <=> v3_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f129,plain,
    ( spl5_15
  <=> sK1 = k3_xboole_0(sK1,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f400,plain,
    ( spl5_26
  <=> v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f436,plain,
    ( v3_pre_topc(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_15
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f435,f130])).

fof(f130,plain,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f435,plain,
    ( v3_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f425,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f425,plain,
    ( v3_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_26 ),
    inference(superposition,[],[f401,f167])).

fof(f167,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f401,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f400])).

fof(f412,plain,
    ( ~ spl5_16
    | spl5_25 ),
    inference(avatar_split_clause,[],[f407,f396,f136])).

fof(f396,plain,
    ( spl5_25
  <=> m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f407,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | spl5_25 ),
    inference(resolution,[],[f397,f165])).

fof(f165,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k9_subset_1(X3,X5,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k9_subset_1(X3,X5,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f51,f53])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f397,plain,
    ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f396])).

fof(f402,plain,
    ( ~ spl5_25
    | ~ spl5_11
    | spl5_26
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f393,f390,f68,f400,f102,f396])).

fof(f102,plain,
    ( spl5_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f68,plain,
    ( spl5_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f390,plain,
    ( spl5_24
  <=> ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f393,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(resolution,[],[f391,f69])).

fof(f69,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f390])).

fof(f392,plain,
    ( ~ spl5_7
    | spl5_24
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f388,f125,f97,f72,f390,f80])).

fof(f80,plain,
    ( spl5_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f72,plain,
    ( spl5_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f97,plain,
    ( spl5_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f125,plain,
    ( spl5_14
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f388,plain,
    ( ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f387,f126])).

fof(f126,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f386,f126])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f385,f98])).

fof(f98,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f54,f73])).

fof(f73,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f140,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f139,f125,f64,f60,f136])).

fof(f60,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f139,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f133,f61])).

fof(f61,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f133,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(superposition,[],[f65,f126])).

% (20640)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f134,plain,
    ( spl5_15
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f131,f125,f112,f129])).

fof(f112,plain,
    ( spl5_12
  <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f131,plain,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK2))
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(superposition,[],[f113,f126])).

fof(f113,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f127,plain,
    ( ~ spl5_7
    | spl5_14
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f122,f72,f125,f80])).

fof(f122,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f95,f73])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f93,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f114,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f110,f64,f60,f112])).

fof(f110,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK2))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f106,f61])).

fof(f106,plain,
    ( sK3 = k3_xboole_0(sK3,u1_struct_0(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f105,f65])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f104,plain,
    ( spl5_11
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f100,f97,f76,f102])).

fof(f76,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(superposition,[],[f77,f98])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f99,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f94,f80,f97])).

fof(f94,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f93,f81])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f83,f60,f56,f85])).

fof(f56,plain,
    ( spl5_1
  <=> v3_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f83,plain,
    ( ~ v3_pre_topc(sK1,sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f57,f61])).

fof(f57,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f82,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27,f26,f25])).

% (20641)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v3_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v3_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f78,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f60])).

fof(f39,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f56])).

fof(f40,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
