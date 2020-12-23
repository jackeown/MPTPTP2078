%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:41 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 224 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  423 (1123 expanded)
%              Number of equality atoms :   77 ( 216 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f111,f114,f195,f204,f694,f704,f742,f777,f804,f814,f846,f1476,f1481])).

fof(f1481,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f1477])).

fof(f1477,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f96,f91,f105,f101,f741,f776])).

fof(f776,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl4_19
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f741,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f739])).

fof(f739,plain,
    ( spl4_17
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f101,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f96,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1476,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_17
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f1458,f811,f739,f99,f94])).

fof(f811,plain,
    ( spl4_20
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1458,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f265,f813])).

fof(f813,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f811])).

fof(f265,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f846,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f816,f739,f108,f99,f94])).

fof(f108,plain,
    ( spl4_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f816,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_17 ),
    inference(superposition,[],[f50,f741])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f814,plain,
    ( spl4_20
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f809,f192,f811])).

fof(f192,plain,
    ( spl4_7
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f809,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f806])).

fof(f806,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f757,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f757,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,k2_tops_1(sK0,sK1),X1),sK1)
        | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1 )
    | ~ spl4_7 ),
    inference(resolution,[],[f751,f537])).

fof(f537,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK3(X11,X12,X11),X12)
      | k4_xboole_0(X11,X12) = X11 ) ),
    inference(global_subsumption,[],[f225,f535])).

fof(f535,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK3(X11,X12,X11),X12)
      | ~ r2_hidden(sK3(X11,X12,X11),X11)
      | k4_xboole_0(X11,X12) = X11 ) ),
    inference(duplicate_literal_removal,[],[f534])).

fof(f534,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK3(X11,X12,X11),X12)
      | ~ r2_hidden(sK3(X11,X12,X11),X11)
      | k4_xboole_0(X11,X12) = X11
      | k4_xboole_0(X11,X12) = X11 ) ),
    inference(resolution,[],[f68,f225])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f751,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl4_7 ),
    inference(superposition,[],[f84,f194])).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f192])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f804,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f96,f101,f773])).

fof(f773,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f772])).

fof(f772,plain,
    ( spl4_18
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f777,plain,
    ( spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f54,f775,f772])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f742,plain,
    ( ~ spl4_4
    | spl4_17
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f734,f692,f99,f94,f739,f104])).

fof(f692,plain,
    ( spl4_16
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f734,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(resolution,[],[f693,f101])).

fof(f693,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f692])).

fof(f704,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f96,f91,f189,f690])).

fof(f690,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f689])).

fof(f689,plain,
    ( spl4_15
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f189,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_6
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f694,plain,
    ( spl4_15
    | spl4_16 ),
    inference(avatar_split_clause,[],[f53,f692,f689])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f204,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f96,f101,f190,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f190,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f195,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f173,f108,f192,f188])).

fof(f173,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f110])).

fof(f110,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f114,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f113,f108,f104])).

fof(f113,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f47,f110])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f111,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f46,f108,f104])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f99])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f94])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (22240)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (22255)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (22245)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (22247)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (22263)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (22242)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (22244)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (22253)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (22246)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (22256)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (22249)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (22243)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (22261)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (22254)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (22269)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (22269)Refutation not found, incomplete strategy% (22269)------------------------------
% 0.22/0.55  % (22269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22269)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22269)Memory used [KB]: 1663
% 0.22/0.55  % (22269)Time elapsed: 0.002 s
% 0.22/0.55  % (22269)------------------------------
% 0.22/0.55  % (22269)------------------------------
% 0.22/0.55  % (22259)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (22248)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (22260)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (22250)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (22262)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (22250)Refutation not found, incomplete strategy% (22250)------------------------------
% 0.22/0.56  % (22250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22250)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22250)Memory used [KB]: 10746
% 0.22/0.56  % (22250)Time elapsed: 0.137 s
% 0.22/0.56  % (22250)------------------------------
% 0.22/0.56  % (22250)------------------------------
% 0.22/0.56  % (22264)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (22252)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (22265)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (22256)Refutation not found, incomplete strategy% (22256)------------------------------
% 0.22/0.56  % (22256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22256)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22256)Memory used [KB]: 10618
% 0.22/0.56  % (22256)Time elapsed: 0.144 s
% 0.22/0.56  % (22256)------------------------------
% 0.22/0.56  % (22256)------------------------------
% 0.22/0.56  % (22258)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (22251)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (22268)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (22268)Refutation not found, incomplete strategy% (22268)------------------------------
% 0.22/0.57  % (22268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (22268)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (22268)Memory used [KB]: 10746
% 0.22/0.57  % (22268)Time elapsed: 0.155 s
% 0.22/0.57  % (22268)------------------------------
% 0.22/0.57  % (22268)------------------------------
% 0.22/0.57  % (22267)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.58  % (22266)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (22241)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.87/0.62  % (22257)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.09/0.67  % (22263)Refutation found. Thanks to Tanya!
% 2.09/0.67  % SZS status Theorem for theBenchmark
% 2.09/0.67  % SZS output start Proof for theBenchmark
% 2.09/0.67  fof(f1482,plain,(
% 2.09/0.67    $false),
% 2.09/0.67    inference(avatar_sat_refutation,[],[f92,f97,f102,f111,f114,f195,f204,f694,f704,f742,f777,f804,f814,f846,f1476,f1481])).
% 2.09/0.67  fof(f1481,plain,(
% 2.09/0.67    ~spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_17 | ~spl4_19),
% 2.09/0.67    inference(avatar_contradiction_clause,[],[f1477])).
% 2.09/0.67  fof(f1477,plain,(
% 2.09/0.67    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_17 | ~spl4_19)),
% 2.09/0.67    inference(unit_resulting_resolution,[],[f96,f91,f105,f101,f741,f776])).
% 2.09/0.67  fof(f776,plain,(
% 2.09/0.67    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl4_19),
% 2.09/0.67    inference(avatar_component_clause,[],[f775])).
% 2.09/0.67  fof(f775,plain,(
% 2.09/0.67    spl4_19 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.09/0.67  fof(f741,plain,(
% 2.09/0.67    sK1 = k1_tops_1(sK0,sK1) | ~spl4_17),
% 2.09/0.67    inference(avatar_component_clause,[],[f739])).
% 2.09/0.67  fof(f739,plain,(
% 2.09/0.67    spl4_17 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.09/0.67  fof(f101,plain,(
% 2.09/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 2.09/0.67    inference(avatar_component_clause,[],[f99])).
% 2.09/0.67  fof(f99,plain,(
% 2.09/0.67    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.09/0.67  fof(f105,plain,(
% 2.09/0.67    ~v3_pre_topc(sK1,sK0) | spl4_4),
% 2.09/0.67    inference(avatar_component_clause,[],[f104])).
% 2.09/0.67  fof(f104,plain,(
% 2.09/0.67    spl4_4 <=> v3_pre_topc(sK1,sK0)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.09/0.67  fof(f91,plain,(
% 2.09/0.67    v2_pre_topc(sK0) | ~spl4_1),
% 2.09/0.67    inference(avatar_component_clause,[],[f89])).
% 2.09/0.67  fof(f89,plain,(
% 2.09/0.67    spl4_1 <=> v2_pre_topc(sK0)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.09/0.67  fof(f96,plain,(
% 2.09/0.67    l1_pre_topc(sK0) | ~spl4_2),
% 2.09/0.67    inference(avatar_component_clause,[],[f94])).
% 2.09/0.67  fof(f94,plain,(
% 2.09/0.67    spl4_2 <=> l1_pre_topc(sK0)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.09/0.67  fof(f1476,plain,(
% 2.09/0.67    ~spl4_2 | ~spl4_3 | spl4_17 | ~spl4_20),
% 2.09/0.67    inference(avatar_split_clause,[],[f1458,f811,f739,f99,f94])).
% 2.09/0.67  fof(f811,plain,(
% 2.09/0.67    spl4_20 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.09/0.67  fof(f1458,plain,(
% 2.09/0.67    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_20),
% 2.09/0.67    inference(superposition,[],[f265,f813])).
% 2.09/0.67  fof(f813,plain,(
% 2.09/0.67    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_20),
% 2.09/0.67    inference(avatar_component_clause,[],[f811])).
% 2.09/0.67  fof(f265,plain,(
% 2.09/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.67    inference(duplicate_literal_removal,[],[f264])).
% 2.09/0.67  fof(f264,plain,(
% 2.09/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.67    inference(superposition,[],[f49,f51])).
% 2.09/0.67  fof(f51,plain,(
% 2.09/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.67    inference(cnf_transformation,[],[f20])).
% 2.09/0.67  fof(f20,plain,(
% 2.09/0.67    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.67    inference(ennf_transformation,[],[f13])).
% 2.09/0.67  fof(f13,axiom,(
% 2.09/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.09/0.67  fof(f49,plain,(
% 2.09/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.67    inference(cnf_transformation,[],[f18])).
% 2.09/0.67  fof(f18,plain,(
% 2.09/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.67    inference(ennf_transformation,[],[f8])).
% 2.09/0.67  fof(f8,axiom,(
% 2.09/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.09/0.67  fof(f846,plain,(
% 2.09/0.67    ~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_17),
% 2.09/0.67    inference(avatar_split_clause,[],[f816,f739,f108,f99,f94])).
% 2.09/0.67  fof(f108,plain,(
% 2.09/0.67    spl4_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.09/0.67  fof(f816,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_17),
% 2.09/0.67    inference(superposition,[],[f50,f741])).
% 2.09/0.67  fof(f50,plain,(
% 2.09/0.67    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.67    inference(cnf_transformation,[],[f19])).
% 2.09/0.67  fof(f19,plain,(
% 2.09/0.67    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.67    inference(ennf_transformation,[],[f11])).
% 2.09/0.67  fof(f11,axiom,(
% 2.09/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.09/0.67  fof(f814,plain,(
% 2.09/0.67    spl4_20 | ~spl4_7),
% 2.09/0.67    inference(avatar_split_clause,[],[f809,f192,f811])).
% 2.09/0.67  fof(f192,plain,(
% 2.09/0.67    spl4_7 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.09/0.67  fof(f809,plain,(
% 2.09/0.67    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_7),
% 2.09/0.67    inference(duplicate_literal_removal,[],[f806])).
% 2.09/0.67  fof(f806,plain,(
% 2.09/0.67    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_7),
% 2.09/0.67    inference(resolution,[],[f757,f225])).
% 2.09/0.67  fof(f225,plain,(
% 2.09/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 2.09/0.67    inference(factoring,[],[f66])).
% 2.09/0.67  fof(f66,plain,(
% 2.09/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.67    inference(cnf_transformation,[],[f40])).
% 2.09/0.67  fof(f40,plain,(
% 2.09/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 2.09/0.67  fof(f39,plain,(
% 2.09/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.09/0.67    introduced(choice_axiom,[])).
% 2.09/0.67  fof(f38,plain,(
% 2.09/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.67    inference(rectify,[],[f37])).
% 2.09/0.67  fof(f37,plain,(
% 2.09/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.67    inference(flattening,[],[f36])).
% 2.09/0.67  fof(f36,plain,(
% 2.09/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.67    inference(nnf_transformation,[],[f3])).
% 2.09/0.67  fof(f3,axiom,(
% 2.09/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.09/0.67  fof(f757,plain,(
% 2.09/0.67    ( ! [X1] : (~r2_hidden(sK3(X1,k2_tops_1(sK0,sK1),X1),sK1) | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1) ) | ~spl4_7),
% 2.09/0.67    inference(resolution,[],[f751,f537])).
% 2.09/0.67  fof(f537,plain,(
% 2.09/0.67    ( ! [X12,X11] : (r2_hidden(sK3(X11,X12,X11),X12) | k4_xboole_0(X11,X12) = X11) )),
% 2.09/0.67    inference(global_subsumption,[],[f225,f535])).
% 2.09/0.67  fof(f535,plain,(
% 2.09/0.67    ( ! [X12,X11] : (r2_hidden(sK3(X11,X12,X11),X12) | ~r2_hidden(sK3(X11,X12,X11),X11) | k4_xboole_0(X11,X12) = X11) )),
% 2.09/0.67    inference(duplicate_literal_removal,[],[f534])).
% 2.09/0.67  fof(f534,plain,(
% 2.09/0.67    ( ! [X12,X11] : (r2_hidden(sK3(X11,X12,X11),X12) | ~r2_hidden(sK3(X11,X12,X11),X11) | k4_xboole_0(X11,X12) = X11 | k4_xboole_0(X11,X12) = X11) )),
% 2.09/0.67    inference(resolution,[],[f68,f225])).
% 2.09/0.67  fof(f68,plain,(
% 2.09/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.67    inference(cnf_transformation,[],[f40])).
% 2.09/0.67  fof(f751,plain,(
% 2.09/0.67    ( ! [X5] : (~r2_hidden(X5,k2_tops_1(sK0,sK1)) | ~r2_hidden(X5,sK1)) ) | ~spl4_7),
% 2.09/0.67    inference(superposition,[],[f84,f194])).
% 2.09/0.67  fof(f194,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_7),
% 2.09/0.67    inference(avatar_component_clause,[],[f192])).
% 2.09/0.67  fof(f84,plain,(
% 2.09/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.09/0.67    inference(equality_resolution,[],[f64])).
% 2.09/0.67  fof(f64,plain,(
% 2.09/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.09/0.67    inference(cnf_transformation,[],[f40])).
% 2.09/0.67  fof(f804,plain,(
% 2.09/0.67    ~spl4_2 | ~spl4_3 | ~spl4_18),
% 2.09/0.67    inference(avatar_contradiction_clause,[],[f800])).
% 2.09/0.67  fof(f800,plain,(
% 2.09/0.67    $false | (~spl4_2 | ~spl4_3 | ~spl4_18)),
% 2.09/0.67    inference(unit_resulting_resolution,[],[f96,f101,f773])).
% 2.09/0.67  fof(f773,plain,(
% 2.09/0.67    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl4_18),
% 2.09/0.67    inference(avatar_component_clause,[],[f772])).
% 2.09/0.67  fof(f772,plain,(
% 2.09/0.67    spl4_18 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.09/0.67  fof(f777,plain,(
% 2.09/0.67    spl4_18 | spl4_19),
% 2.09/0.67    inference(avatar_split_clause,[],[f54,f775,f772])).
% 2.09/0.67  fof(f54,plain,(
% 2.09/0.67    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.67    inference(cnf_transformation,[],[f24])).
% 2.09/0.67  fof(f24,plain,(
% 2.09/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.67    inference(flattening,[],[f23])).
% 2.09/0.67  fof(f23,plain,(
% 2.09/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.67    inference(ennf_transformation,[],[f12])).
% 2.09/0.67  fof(f12,axiom,(
% 2.09/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 2.09/0.67  fof(f742,plain,(
% 2.09/0.67    ~spl4_4 | spl4_17 | ~spl4_2 | ~spl4_3 | ~spl4_16),
% 2.09/0.67    inference(avatar_split_clause,[],[f734,f692,f99,f94,f739,f104])).
% 2.09/0.67  fof(f692,plain,(
% 2.09/0.67    spl4_16 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.09/0.67  fof(f734,plain,(
% 2.09/0.67    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_16)),
% 2.09/0.67    inference(resolution,[],[f693,f101])).
% 2.09/0.67  fof(f693,plain,(
% 2.09/0.67    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl4_16),
% 2.09/0.67    inference(avatar_component_clause,[],[f692])).
% 2.09/0.67  fof(f704,plain,(
% 2.09/0.67    ~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_15),
% 2.09/0.67    inference(avatar_contradiction_clause,[],[f698])).
% 2.09/0.67  fof(f698,plain,(
% 2.09/0.67    $false | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_15)),
% 2.09/0.67    inference(unit_resulting_resolution,[],[f96,f91,f189,f690])).
% 2.09/0.67  fof(f690,plain,(
% 2.09/0.67    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl4_15),
% 2.09/0.67    inference(avatar_component_clause,[],[f689])).
% 2.09/0.67  fof(f689,plain,(
% 2.09/0.67    spl4_15 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.09/0.67  fof(f189,plain,(
% 2.09/0.67    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 2.09/0.67    inference(avatar_component_clause,[],[f188])).
% 2.09/0.67  fof(f188,plain,(
% 2.09/0.67    spl4_6 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.09/0.67  fof(f694,plain,(
% 2.09/0.67    spl4_15 | spl4_16),
% 2.09/0.67    inference(avatar_split_clause,[],[f53,f692,f689])).
% 2.09/0.67  fof(f53,plain,(
% 2.09/0.67    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.67    inference(cnf_transformation,[],[f24])).
% 2.09/0.67  fof(f204,plain,(
% 2.09/0.67    ~spl4_2 | ~spl4_3 | spl4_6),
% 2.09/0.67    inference(avatar_contradiction_clause,[],[f202])).
% 2.09/0.67  fof(f202,plain,(
% 2.09/0.67    $false | (~spl4_2 | ~spl4_3 | spl4_6)),
% 2.09/0.67    inference(unit_resulting_resolution,[],[f96,f101,f190,f52])).
% 2.09/0.67  fof(f52,plain,(
% 2.09/0.67    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.67    inference(cnf_transformation,[],[f22])).
% 2.09/0.67  fof(f22,plain,(
% 2.09/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.09/0.67    inference(flattening,[],[f21])).
% 2.09/0.67  fof(f21,plain,(
% 2.09/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.09/0.67    inference(ennf_transformation,[],[f10])).
% 2.09/0.67  fof(f10,axiom,(
% 2.09/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.09/0.67  fof(f190,plain,(
% 2.09/0.67    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_6),
% 2.09/0.67    inference(avatar_component_clause,[],[f188])).
% 2.09/0.67  fof(f195,plain,(
% 2.09/0.67    ~spl4_6 | spl4_7 | ~spl4_5),
% 2.09/0.67    inference(avatar_split_clause,[],[f173,f108,f192,f188])).
% 2.09/0.67  fof(f173,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 2.09/0.67    inference(superposition,[],[f49,f110])).
% 2.09/0.67  fof(f110,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_5),
% 2.09/0.67    inference(avatar_component_clause,[],[f108])).
% 2.09/0.67  fof(f114,plain,(
% 2.09/0.67    ~spl4_4 | ~spl4_5),
% 2.09/0.67    inference(avatar_split_clause,[],[f113,f108,f104])).
% 2.09/0.67  fof(f113,plain,(
% 2.09/0.67    ~v3_pre_topc(sK1,sK0) | ~spl4_5),
% 2.09/0.67    inference(trivial_inequality_removal,[],[f112])).
% 2.09/0.67  fof(f112,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl4_5),
% 2.09/0.67    inference(forward_demodulation,[],[f47,f110])).
% 2.09/0.67  fof(f47,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.09/0.67    inference(cnf_transformation,[],[f30])).
% 2.09/0.67  fof(f30,plain,(
% 2.09/0.67    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.09/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 2.09/0.67  fof(f28,plain,(
% 2.09/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.09/0.67    introduced(choice_axiom,[])).
% 2.09/0.67  fof(f29,plain,(
% 2.09/0.67    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.09/0.67    introduced(choice_axiom,[])).
% 2.09/0.67  fof(f27,plain,(
% 2.09/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.67    inference(flattening,[],[f26])).
% 2.09/0.67  fof(f26,plain,(
% 2.09/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.67    inference(nnf_transformation,[],[f17])).
% 2.09/0.67  fof(f17,plain,(
% 2.09/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.67    inference(flattening,[],[f16])).
% 2.09/0.67  fof(f16,plain,(
% 2.09/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.09/0.67    inference(ennf_transformation,[],[f15])).
% 2.09/0.67  fof(f15,negated_conjecture,(
% 2.09/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.09/0.67    inference(negated_conjecture,[],[f14])).
% 2.09/0.67  fof(f14,conjecture,(
% 2.09/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.09/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.09/0.67  fof(f111,plain,(
% 2.09/0.67    spl4_4 | spl4_5),
% 2.09/0.67    inference(avatar_split_clause,[],[f46,f108,f104])).
% 2.09/0.67  fof(f46,plain,(
% 2.09/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.09/0.67    inference(cnf_transformation,[],[f30])).
% 2.09/0.67  fof(f102,plain,(
% 2.09/0.67    spl4_3),
% 2.09/0.67    inference(avatar_split_clause,[],[f45,f99])).
% 2.09/0.67  fof(f45,plain,(
% 2.09/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.67    inference(cnf_transformation,[],[f30])).
% 2.09/0.67  fof(f97,plain,(
% 2.09/0.67    spl4_2),
% 2.09/0.67    inference(avatar_split_clause,[],[f44,f94])).
% 2.09/0.67  fof(f44,plain,(
% 2.09/0.67    l1_pre_topc(sK0)),
% 2.09/0.67    inference(cnf_transformation,[],[f30])).
% 2.09/0.67  fof(f92,plain,(
% 2.09/0.67    spl4_1),
% 2.09/0.67    inference(avatar_split_clause,[],[f43,f89])).
% 2.09/0.67  fof(f43,plain,(
% 2.09/0.67    v2_pre_topc(sK0)),
% 2.09/0.67    inference(cnf_transformation,[],[f30])).
% 2.09/0.67  % SZS output end Proof for theBenchmark
% 2.09/0.67  % (22263)------------------------------
% 2.09/0.67  % (22263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.67  % (22263)Termination reason: Refutation
% 2.09/0.67  
% 2.09/0.67  % (22263)Memory used [KB]: 12025
% 2.09/0.67  % (22263)Time elapsed: 0.233 s
% 2.09/0.67  % (22263)------------------------------
% 2.09/0.67  % (22263)------------------------------
% 2.09/0.67  % (22239)Success in time 0.304 s
%------------------------------------------------------------------------------
