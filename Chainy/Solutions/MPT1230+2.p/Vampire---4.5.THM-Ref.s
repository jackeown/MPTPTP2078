%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1230+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 3.83s
% Output     : Refutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 281 expanded)
%              Number of leaves         :   20 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  494 (2487 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7032,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3566,f3576,f3581,f3586,f3610,f3615,f3620,f3625,f3634,f5417,f6889,f6915,f6950,f7031])).

fof(f7031,plain,
    ( spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9
    | ~ spl101_15
    | ~ spl101_87
    | ~ spl101_88
    | ~ spl101_89 ),
    inference(avatar_contradiction_clause,[],[f7030])).

fof(f7030,plain,
    ( $false
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9
    | ~ spl101_15
    | ~ spl101_87
    | ~ spl101_88
    | ~ spl101_89 ),
    inference(subsumption_resolution,[],[f6951,f5437])).

fof(f5437,plain,
    ( m1_subset_1(sK22(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(unit_resulting_resolution,[],[f3575,f3565,f3580,f3585,f3605,f2860])).

fof(f2860,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK22(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f2582,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK22(X0,X1,X2))
                    & r2_hidden(X2,sK22(X0,X1,X2))
                    & v3_pre_topc(sK22(X0,X1,X2),X0)
                    & m1_subset_1(sK22(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f2580,f2581])).

fof(f2581,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK22(X0,X1,X2))
        & r2_hidden(X2,sK22(X0,X1,X2))
        & v3_pre_topc(sK22(X0,X1,X2),X0)
        & m1_subset_1(sK22(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2580,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2579])).

fof(f2579,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2578])).

fof(f2578,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2188])).

fof(f2188,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2187])).

fof(f2187,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1845])).

fof(f1845,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f3605,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl101_9 ),
    inference(avatar_component_clause,[],[f3603])).

fof(f3603,plain,
    ( spl101_9
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_9])])).

fof(f3585,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl101_5 ),
    inference(avatar_component_clause,[],[f3583])).

fof(f3583,plain,
    ( spl101_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_5])])).

fof(f3580,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl101_4 ),
    inference(avatar_component_clause,[],[f3578])).

fof(f3578,plain,
    ( spl101_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_4])])).

fof(f3565,plain,
    ( ~ v2_struct_0(sK0)
    | spl101_1 ),
    inference(avatar_component_clause,[],[f3563])).

fof(f3563,plain,
    ( spl101_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_1])])).

fof(f3575,plain,
    ( l1_pre_topc(sK0)
    | ~ spl101_3 ),
    inference(avatar_component_clause,[],[f3573])).

fof(f3573,plain,
    ( spl101_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_3])])).

fof(f6951,plain,
    ( ~ m1_subset_1(sK22(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl101_15
    | ~ spl101_87
    | ~ spl101_88
    | ~ spl101_89 ),
    inference(unit_resulting_resolution,[],[f6914,f6888,f6949,f3633])).

fof(f3633,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(sK1,X4)
        | ~ r2_hidden(sK2,X4) )
    | ~ spl101_15 ),
    inference(avatar_component_clause,[],[f3632])).

fof(f3632,plain,
    ( spl101_15
  <=> ! [X4] :
        ( ~ r1_xboole_0(sK1,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X4,sK0)
        | ~ r2_hidden(sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_15])])).

fof(f6949,plain,
    ( r1_xboole_0(sK1,sK22(sK0,sK1,sK2))
    | ~ spl101_89 ),
    inference(avatar_component_clause,[],[f6947])).

fof(f6947,plain,
    ( spl101_89
  <=> r1_xboole_0(sK1,sK22(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_89])])).

fof(f6888,plain,
    ( v3_pre_topc(sK22(sK0,sK1,sK2),sK0)
    | ~ spl101_87 ),
    inference(avatar_component_clause,[],[f6886])).

fof(f6886,plain,
    ( spl101_87
  <=> v3_pre_topc(sK22(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_87])])).

fof(f6914,plain,
    ( r2_hidden(sK2,sK22(sK0,sK1,sK2))
    | ~ spl101_88 ),
    inference(avatar_component_clause,[],[f6912])).

fof(f6912,plain,
    ( spl101_88
  <=> r2_hidden(sK2,sK22(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_88])])).

fof(f6950,plain,
    ( spl101_89
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(avatar_split_clause,[],[f5440,f3603,f3583,f3578,f3573,f3563,f6947])).

fof(f5440,plain,
    ( r1_xboole_0(sK1,sK22(sK0,sK1,sK2))
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(unit_resulting_resolution,[],[f3575,f3565,f3580,f3585,f3605,f2863])).

fof(f2863,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_xboole_0(X1,sK22(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f6915,plain,
    ( spl101_88
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(avatar_split_clause,[],[f5439,f3603,f3583,f3578,f3573,f3563,f6912])).

fof(f5439,plain,
    ( r2_hidden(sK2,sK22(sK0,sK1,sK2))
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(unit_resulting_resolution,[],[f3575,f3565,f3580,f3585,f3605,f2862])).

fof(f2862,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(X2,sK22(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f6889,plain,
    ( spl101_87
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(avatar_split_clause,[],[f5438,f3603,f3583,f3578,f3573,f3563,f6886])).

fof(f5438,plain,
    ( v3_pre_topc(sK22(sK0,sK1,sK2),sK0)
    | spl101_1
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | spl101_9 ),
    inference(unit_resulting_resolution,[],[f3575,f3565,f3580,f3585,f3605,f2861])).

fof(f2861,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK22(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f5417,plain,
    ( ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | ~ spl101_9
    | ~ spl101_10
    | ~ spl101_11
    | ~ spl101_12
    | ~ spl101_13 ),
    inference(avatar_contradiction_clause,[],[f5416])).

fof(f5416,plain,
    ( $false
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | ~ spl101_9
    | ~ spl101_10
    | ~ spl101_11
    | ~ spl101_12
    | ~ spl101_13 ),
    inference(subsumption_resolution,[],[f5402,f3624])).

fof(f3624,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl101_13 ),
    inference(avatar_component_clause,[],[f3622])).

fof(f3622,plain,
    ( spl101_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_13])])).

fof(f5402,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl101_3
    | ~ spl101_4
    | ~ spl101_5
    | ~ spl101_9
    | ~ spl101_10
    | ~ spl101_11
    | ~ spl101_12 ),
    inference(unit_resulting_resolution,[],[f3619,f3614,f3609,f3575,f3580,f3585,f3604,f2859])).

fof(f2859,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X1,X4) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3604,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl101_9 ),
    inference(avatar_component_clause,[],[f3603])).

fof(f3609,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl101_10 ),
    inference(avatar_component_clause,[],[f3607])).

fof(f3607,plain,
    ( spl101_10
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_10])])).

fof(f3614,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl101_11 ),
    inference(avatar_component_clause,[],[f3612])).

fof(f3612,plain,
    ( spl101_11
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_11])])).

fof(f3619,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl101_12 ),
    inference(avatar_component_clause,[],[f3617])).

fof(f3617,plain,
    ( spl101_12
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_12])])).

fof(f3634,plain,
    ( spl101_9
    | spl101_15 ),
    inference(avatar_split_clause,[],[f2766,f3632,f3603])).

fof(f2766,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(sK1,X4)
      | ~ r2_hidden(sK2,X4)
      | ~ v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f2544])).

fof(f2544,plain,
    ( ( ( r1_xboole_0(sK1,sK3)
        & r2_hidden(sK2,sK3)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(sK1,X4)
          | ~ r2_hidden(sK2,X4)
          | ~ v3_pre_topc(X4,sK0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2539,f2543,f2542,f2541,f2540])).

fof(f2540,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,sK0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2541,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X1,X3)
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,sK0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(sK1,X3)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(sK1,X4)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,sK0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2542,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( r1_xboole_0(sK1,X3)
              & r2_hidden(X2,X3)
              & v3_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(sK1,X4)
              | ~ r2_hidden(X2,X4)
              | ~ v3_pre_topc(X4,sK0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ? [X3] :
            ( r1_xboole_0(sK1,X3)
            & r2_hidden(sK2,X3)
            & v3_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(sK1,X4)
            | ~ r2_hidden(sK2,X4)
            | ~ v3_pre_topc(X4,sK0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2543,plain,
    ( ? [X3] :
        ( r1_xboole_0(sK1,X3)
        & r2_hidden(sK2,X3)
        & v3_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r1_xboole_0(sK1,sK3)
      & r2_hidden(sK2,sK3)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2539,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f2538])).

fof(f2538,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2537])).

fof(f2537,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2113])).

fof(f2113,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2112])).

fof(f2112,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2106])).

fof(f2106,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2105])).

fof(f2105,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

fof(f3625,plain,
    ( ~ spl101_9
    | spl101_13 ),
    inference(avatar_split_clause,[],[f2767,f3622,f3603])).

fof(f2767,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3620,plain,
    ( ~ spl101_9
    | spl101_12 ),
    inference(avatar_split_clause,[],[f2770,f3617,f3603])).

fof(f2770,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3615,plain,
    ( ~ spl101_9
    | spl101_11 ),
    inference(avatar_split_clause,[],[f2769,f3612,f3603])).

fof(f2769,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3610,plain,
    ( ~ spl101_9
    | spl101_10 ),
    inference(avatar_split_clause,[],[f2768,f3607,f3603])).

fof(f2768,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3586,plain,(
    spl101_5 ),
    inference(avatar_split_clause,[],[f2764,f3583])).

fof(f2764,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3581,plain,(
    spl101_4 ),
    inference(avatar_split_clause,[],[f2765,f3578])).

fof(f2765,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3576,plain,(
    spl101_3 ),
    inference(avatar_split_clause,[],[f2763,f3573])).

fof(f2763,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2544])).

fof(f3566,plain,(
    ~ spl101_1 ),
    inference(avatar_split_clause,[],[f2761,f3563])).

fof(f2761,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2544])).
%------------------------------------------------------------------------------
