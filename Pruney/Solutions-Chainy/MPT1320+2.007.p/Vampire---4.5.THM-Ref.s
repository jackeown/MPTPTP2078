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
% DateTime   : Thu Dec  3 13:13:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 175 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  347 ( 760 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f87,f113,f194,f211,f231,f250,f288])).

fof(f288,plain,
    ( ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | spl10_15
    | ~ spl10_17 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | spl10_15
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f267,f249])).

fof(f249,plain,
    ( m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl10_17
  <=> m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f267,plain,
    ( ~ m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f86,f230,f76,f71,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | sP3(X2,X0,X1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP3(X2,X0,X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14,f13,f12])).

fof(f12,plain,(
    ! [X4,X1,X0,X2] :
      ( sP0(X4,X1,X0,X2)
    <=> ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
          & r2_hidden(X5,X2)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X2,X0,X1,X4,X3] :
      ( sP1(X2,X0,X1,X4,X3)
    <=> ( r2_hidden(X4,X3)
      <=> sP0(X4,X1,X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X3,X1,X0,X2] :
      ( sP2(X3,X1,X0,X2)
    <=> ! [X4] :
          ( sP1(X2,X0,X1,X4,X3)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f15,plain,(
    ! [X2,X0,X1,X3] :
      ( ( k1_tops_2(X0,X1,X2) = X3
      <=> sP2(X3,X1,X0,X2) )
      | ~ sP3(X2,X0,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

fof(f71,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_3
  <=> m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f76,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl10_4
  <=> m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f230,plain,
    ( ~ sP3(sK7,sK4,sK6,k1_tops_2(sK4,sK6,sK7))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_15
  <=> sP3(sK7,sK4,sK6,k1_tops_2(sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f86,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl10_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f250,plain,
    ( spl10_17
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f235,f84,f74,f69,f247])).

fof(f235,plain,
    ( m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f86,f76,f71,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f231,plain,
    ( ~ spl10_15
    | spl10_12 ),
    inference(avatar_split_clause,[],[f212,f208,f228])).

fof(f208,plain,
    ( spl10_12
  <=> sP2(k1_tops_2(sK4,sK6,sK7),sK6,sK4,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f212,plain,
    ( ~ sP3(sK7,sK4,sK6,k1_tops_2(sK4,sK6,sK7))
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f210,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2,k1_tops_2(X1,X2,X0))
      | sP2(k1_tops_2(X1,X2,X0),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | k1_tops_2(X1,X2,X0) != X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_tops_2(X1,X2,X0) = X3
          | ~ sP2(X3,X2,X1,X0) )
        & ( sP2(X3,X2,X1,X0)
          | k1_tops_2(X1,X2,X0) != X3 ) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1,X3] :
      ( ( ( k1_tops_2(X0,X1,X2) = X3
          | ~ sP2(X3,X1,X0,X2) )
        & ( sP2(X3,X1,X0,X2)
          | k1_tops_2(X0,X1,X2) != X3 ) )
      | ~ sP3(X2,X0,X1,X3) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f210,plain,
    ( ~ sP2(k1_tops_2(sK4,sK6,sK7),sK6,sK4,sK7)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f211,plain,
    ( ~ spl10_12
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f205,f191,f110,f208])).

fof(f110,plain,
    ( spl10_7
  <=> sP1(sK7,sK4,sK6,k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f191,plain,
    ( spl10_10
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f205,plain,
    ( ~ sP2(k1_tops_2(sK4,sK6,sK7),sK6,sK4,sK7)
    | spl10_7
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f112,f193,f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1))))
      | sP1(X3,X2,X1,X5,X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ~ sP1(X3,X2,X1,sK8(X0,X1,X2,X3),X0)
          & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) ) )
      & ( ! [X5] :
            ( sP1(X3,X2,X1,X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ sP1(X3,X2,X1,X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) )
     => ( ~ sP1(X3,X2,X1,sK8(X0,X1,X2,X3),X0)
        & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ sP1(X3,X2,X1,X4,X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) ) )
      & ( ! [X5] :
            ( sP1(X3,X2,X1,X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP2(X3,X1,X0,X2)
        | ? [X4] :
            ( ~ sP1(X2,X0,X1,X4,X3)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( sP1(X2,X0,X1,X4,X3)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP2(X3,X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f193,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f112,plain,
    ( ~ sP1(sK7,sK4,sK6,k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))
    | spl10_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f194,plain,
    ( spl10_10
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f153,f84,f79,f74,f191])).

fof(f79,plain,
    ( spl10_5
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f153,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f86,f81,f76,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(f81,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f113,plain,
    ( ~ spl10_7
    | spl10_1
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f107,f79,f64,f59,f110])).

fof(f59,plain,
    ( spl10_1
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f64,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f107,plain,
    ( ~ sP1(sK7,sK4,sK6,k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f61,f102,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X3,X2,X1,X0)
      | r2_hidden(X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ sP0(X3,X2,X1,X0)
            | ~ r2_hidden(X3,X4) )
          & ( sP0(X3,X2,X1,X0)
            | r2_hidden(X3,X4) ) ) )
      & ( ( ( r2_hidden(X3,X4)
            | ~ sP0(X3,X2,X1,X0) )
          & ( sP0(X3,X2,X1,X0)
            | ~ r2_hidden(X3,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1,X4,X3] :
      ( ( sP1(X2,X0,X1,X4,X3)
        | ( ( ~ sP0(X4,X1,X0,X2)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X1,X0,X2)
            | r2_hidden(X4,X3) ) ) )
      & ( ( ( r2_hidden(X4,X3)
            | ~ sP0(X4,X1,X0,X2) )
          & ( sP0(X4,X1,X0,X2)
            | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X0,X1,X4,X3) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f102,plain,
    ( ! [X0] : sP0(k9_subset_1(u1_struct_0(sK4),sK5,X0),X0,sK4,sK7)
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f66,f81,f57])).

fof(f57,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(k9_subset_1(u1_struct_0(X2),X4,X1),X1,X2,X3)
      | ~ r2_hidden(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k9_subset_1(u1_struct_0(X2),X4,X1) != X0
      | ~ r2_hidden(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( k9_subset_1(u1_struct_0(X2),X4,X1) != X0
            | ~ r2_hidden(X4,X3)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),sK9(X0,X1,X2,X3),X1) = X0
          & r2_hidden(sK9(X0,X1,X2,X3),X3)
          & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X2),X5,X1) = X0
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),sK9(X0,X1,X2,X3),X1) = X0
        & r2_hidden(sK9(X0,X1,X2,X3),X3)
        & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( k9_subset_1(u1_struct_0(X2),X4,X1) != X0
            | ~ r2_hidden(X4,X3)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X5] :
            ( k9_subset_1(u1_struct_0(X2),X5,X1) = X0
            & r2_hidden(X5,X3)
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X4,X1,X0,X2] :
      ( ( sP0(X4,X1,X0,X2)
        | ! [X5] :
            ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X5] :
            ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
            & r2_hidden(X5,X2)
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X4,X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f66,plain,
    ( r2_hidden(sK5,sK7)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f61,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f87,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))
    & r2_hidden(sK5,sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f7,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),X1,X2),k1_tops_2(sK4,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),X1,X2),k1_tops_2(sK4,X2,X3))
                & r2_hidden(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,X2),k1_tops_2(sK4,X2,X3))
              & r2_hidden(sK5,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,X2),k1_tops_2(sK4,X2,X3))
            & r2_hidden(sK5,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,X3))
          & r2_hidden(sK5,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,X3))
        & r2_hidden(sK5,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
   => ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))
      & r2_hidden(sK5,sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

fof(f82,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f38,plain,(
    r2_hidden(sK5,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f39,f59])).

fof(f39,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (22014)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (22019)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (22003)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (22019)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f87,f113,f194,f211,f231,f250,f288])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ~spl10_3 | ~spl10_4 | ~spl10_6 | spl10_15 | ~spl10_17),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f287])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    $false | (~spl10_3 | ~spl10_4 | ~spl10_6 | spl10_15 | ~spl10_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f267,f249])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))) | ~spl10_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f247])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    spl10_17 <=> m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))) | (~spl10_3 | ~spl10_4 | ~spl10_6 | spl10_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f86,f230,f76,f71,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | sP3(X2,X0,X1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP3(X2,X0,X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(definition_folding,[],[f9,f15,f14,f13,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X4,X1,X0,X2] : (sP0(X4,X1,X0,X2) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X2,X0,X1,X4,X3] : (sP1(X2,X0,X1,X4,X3) <=> (r2_hidden(X4,X3) <=> sP0(X4,X1,X0,X2)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X3,X1,X0,X2] : (sP2(X3,X1,X0,X2) <=> ! [X4] : (sP1(X2,X0,X1,X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X2,X0,X1,X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> sP2(X3,X1,X0,X2)) | ~sP3(X2,X0,X1,X3))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | ~spl10_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl10_3 <=> m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | ~spl10_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl10_4 <=> m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~sP3(sK7,sK4,sK6,k1_tops_2(sK4,sK6,sK7)) | spl10_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f228])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    spl10_15 <=> sP3(sK7,sK4,sK6,k1_tops_2(sK4,sK6,sK7))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    l1_pre_topc(sK4) | ~spl10_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl10_6 <=> l1_pre_topc(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    spl10_17 | ~spl10_3 | ~spl10_4 | ~spl10_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f235,f84,f74,f69,f247])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    m1_subset_1(k1_tops_2(sK4,sK6,sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))) | (~spl10_3 | ~spl10_4 | ~spl10_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f86,f76,f71,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~spl10_15 | spl10_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f212,f208,f228])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl10_12 <=> sP2(k1_tops_2(sK4,sK6,sK7),sK6,sK4,sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~sP3(sK7,sK4,sK6,k1_tops_2(sK4,sK6,sK7)) | spl10_12),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f210,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2,k1_tops_2(X1,X2,X0)) | sP2(k1_tops_2(X1,X2,X0),X2,X1,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | k1_tops_2(X1,X2,X0) != X3 | ~sP3(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (((k1_tops_2(X1,X2,X0) = X3 | ~sP2(X3,X2,X1,X0)) & (sP2(X3,X2,X1,X0) | k1_tops_2(X1,X2,X0) != X3)) | ~sP3(X0,X1,X2,X3))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X2,X0,X1,X3] : (((k1_tops_2(X0,X1,X2) = X3 | ~sP2(X3,X1,X0,X2)) & (sP2(X3,X1,X0,X2) | k1_tops_2(X0,X1,X2) != X3)) | ~sP3(X2,X0,X1,X3))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~sP2(k1_tops_2(sK4,sK6,sK7),sK6,sK4,sK7) | spl10_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f208])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ~spl10_12 | spl10_7 | ~spl10_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f205,f191,f110,f208])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl10_7 <=> sP1(sK7,sK4,sK6,k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl10_10 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~sP2(k1_tops_2(sK4,sK6,sK7),sK6,sK4,sK7) | (spl10_7 | ~spl10_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f112,f193,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))) | sP1(X3,X2,X1,X5,X0) | ~sP2(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (~sP1(X3,X2,X1,sK8(X0,X1,X2,X3),X0) & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))))) & (! [X5] : (sP1(X3,X2,X1,X5,X0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1))))) | ~sP2(X0,X1,X2,X3)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X4] : (~sP1(X3,X2,X1,X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1))))) => (~sP1(X3,X2,X1,sK8(X0,X1,X2,X3),X0) & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1))))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : (~sP1(X3,X2,X1,X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1)))))) & (! [X5] : (sP1(X3,X2,X1,X5,X0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X1))))) | ~sP2(X0,X1,X2,X3)))),
% 0.21/0.49    inference(rectify,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X3,X1,X0,X2] : ((sP2(X3,X1,X0,X2) | ? [X4] : (~sP1(X2,X0,X1,X4,X3) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (sP1(X2,X0,X1,X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~sP2(X3,X1,X0,X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    m1_subset_1(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))) | ~spl10_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~sP1(sK7,sK4,sK6,k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) | spl10_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl10_10 | ~spl10_4 | ~spl10_5 | ~spl10_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f153,f84,f79,f74,f191])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl10_5 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    m1_subset_1(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK6)))) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f86,f81,f76,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~spl10_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~spl10_7 | spl10_1 | ~spl10_2 | ~spl10_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f107,f79,f64,f59,f110])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl10_1 <=> r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl10_2 <=> r2_hidden(sK5,sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~sP1(sK7,sK4,sK6,k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) | (spl10_1 | ~spl10_2 | ~spl10_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f61,f102,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X3,X2,X1,X0) | r2_hidden(X3,X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~sP0(X3,X2,X1,X0) | ~r2_hidden(X3,X4)) & (sP0(X3,X2,X1,X0) | r2_hidden(X3,X4)))) & (((r2_hidden(X3,X4) | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | ~r2_hidden(X3,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.49    inference(rectify,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X2,X0,X1,X4,X3] : ((sP1(X2,X0,X1,X4,X3) | ((~sP0(X4,X1,X0,X2) | ~r2_hidden(X4,X3)) & (sP0(X4,X1,X0,X2) | r2_hidden(X4,X3)))) & (((r2_hidden(X4,X3) | ~sP0(X4,X1,X0,X2)) & (sP0(X4,X1,X0,X2) | ~r2_hidden(X4,X3))) | ~sP1(X2,X0,X1,X4,X3)))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(k9_subset_1(u1_struct_0(sK4),sK5,X0),X0,sK4,sK7)) ) | (~spl10_2 | ~spl10_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f66,f81,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X4,X2,X3,X1] : (sP0(k9_subset_1(u1_struct_0(X2),X4,X1),X1,X2,X3) | ~r2_hidden(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | k9_subset_1(u1_struct_0(X2),X4,X1) != X0 | ~r2_hidden(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (k9_subset_1(u1_struct_0(X2),X4,X1) != X0 | ~r2_hidden(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),sK9(X0,X1,X2,X3),X1) = X0 & r2_hidden(sK9(X0,X1,X2,X3),X3) & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X2),X5,X1) = X0 & r2_hidden(X5,X3) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),sK9(X0,X1,X2,X3),X1) = X0 & r2_hidden(sK9(X0,X1,X2,X3),X3) & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (k9_subset_1(u1_struct_0(X2),X4,X1) != X0 | ~r2_hidden(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X5] : (k9_subset_1(u1_struct_0(X2),X5,X1) = X0 & r2_hidden(X5,X3) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.49    inference(rectify,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X4,X1,X0,X2] : ((sP0(X4,X1,X0,X2) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X4,X1,X0,X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    r2_hidden(sK5,sK7) | ~spl10_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) | spl10_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl10_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f84])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    l1_pre_topc(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    (((~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) & r2_hidden(sK5,sK7) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f7,f20,f19,f18,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK4),X1,X2),k1_tops_2(sK4,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK4),X1,X2),k1_tops_2(sK4,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,X2),k1_tops_2(sK4,X2,X3)) & r2_hidden(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,X2),k1_tops_2(sK4,X2,X3)) & r2_hidden(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,X3)) & r2_hidden(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,X3)) & r2_hidden(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) => (~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7)) & r2_hidden(sK5,sK7) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl10_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f79])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl10_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f74])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl10_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f69])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl10_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f64])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    r2_hidden(sK5,sK7)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~spl10_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f59])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ~r2_hidden(k9_subset_1(u1_struct_0(sK4),sK5,sK6),k1_tops_2(sK4,sK6,sK7))),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22019)------------------------------
% 0.21/0.49  % (22019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22019)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22019)Memory used [KB]: 11001
% 0.21/0.49  % (22019)Time elapsed: 0.023 s
% 0.21/0.49  % (22019)------------------------------
% 0.21/0.49  % (22019)------------------------------
% 0.21/0.49  % (21994)Success in time 0.133 s
%------------------------------------------------------------------------------
