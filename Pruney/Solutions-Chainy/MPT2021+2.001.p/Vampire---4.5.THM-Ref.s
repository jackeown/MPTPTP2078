%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 392 expanded)
%              Number of leaves         :   40 ( 176 expanded)
%              Depth                    :   13
%              Number of atoms          :  717 (1839 expanded)
%              Number of equality atoms :   51 ( 252 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f86,f91,f97,f104,f113,f117,f128,f132,f138,f151,f156,f164,f182,f199,f209,f214,f221,f301,f314,f330,f336,f347,f354])).

fof(f354,plain,
    ( ~ spl5_2
    | spl5_6
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl5_2
    | spl5_6
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f352,f90])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f352,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_2
    | spl5_6
    | ~ spl5_24
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f351,f198])).

fof(f198,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_24
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f351,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_2
    | spl5_6
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f350,f64])).

fof(f64,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | spl5_6
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f348,f85])).

fof(f85,plain,
    ( ~ v2_tops_2(sK2,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_6
  <=> v2_tops_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f348,plain,
    ( v2_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl5_41 ),
    inference(resolution,[],[f346,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f346,plain,
    ( v4_pre_topc(sK4(sK1,sK2),sK1)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl5_41
  <=> v4_pre_topc(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f347,plain,
    ( spl5_41
    | ~ spl5_17
    | ~ spl5_24
    | ~ spl5_39
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f342,f328,f324,f196,f153,f344])).

fof(f153,plain,
    ( spl5_17
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f324,plain,
    ( spl5_39
  <=> m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f328,plain,
    ( spl5_40
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v4_pre_topc(sK4(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f342,plain,
    ( v4_pre_topc(sK4(sK1,sK2),sK1)
    | ~ spl5_17
    | ~ spl5_24
    | ~ spl5_39
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f341,f325])).

fof(f325,plain,
    ( m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f324])).

fof(f341,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK4(sK1,sK2),sK1)
    | ~ spl5_17
    | ~ spl5_24
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f339,f198])).

fof(f339,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(sK4(sK1,sK2),sK1)
    | ~ spl5_17
    | ~ spl5_40 ),
    inference(resolution,[],[f329,f155])).

fof(f155,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK1,sK2),X0) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f328])).

fof(f336,plain,
    ( spl5_6
    | ~ spl5_7
    | ~ spl5_36
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl5_6
    | ~ spl5_7
    | ~ spl5_36
    | spl5_39 ),
    inference(subsumption_resolution,[],[f334,f90])).

fof(f334,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_6
    | ~ spl5_36
    | spl5_39 ),
    inference(subsumption_resolution,[],[f332,f85])).

fof(f332,plain,
    ( v2_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_36
    | spl5_39 ),
    inference(resolution,[],[f326,f300])).

fof(f300,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl5_36
  <=> ! [X3] :
        ( m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f326,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f324])).

fof(f330,plain,
    ( ~ spl5_39
    | spl5_40
    | ~ spl5_1
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f316,f311,f57,f328,f324])).

fof(f57,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f311,plain,
    ( spl5_37
  <=> v4_pre_topc(sK4(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f315,f59])).

fof(f59,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_37 ),
    inference(resolution,[],[f313,f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f313,plain,
    ( v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( spl5_37
    | ~ spl5_1
    | ~ spl5_4
    | spl5_6
    | ~ spl5_7
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f309,f299,f207,f88,f83,f72,f57,f311])).

fof(f72,plain,
    ( spl5_4
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f207,plain,
    ( spl5_25
  <=> ! [X0] :
        ( v4_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f309,plain,
    ( v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ spl5_1
    | ~ spl5_4
    | spl5_6
    | ~ spl5_7
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f308,f59])).

fof(f308,plain,
    ( v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | spl5_6
    | ~ spl5_7
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f307,f74])).

fof(f74,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f307,plain,
    ( v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ v2_tops_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_6
    | ~ spl5_7
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f306,f90])).

fof(f306,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ v2_tops_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_6
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f305,f85])).

fof(f305,plain,
    ( v2_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ v2_tops_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( v2_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK4(sK1,sK2),sK0)
    | ~ v2_tops_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(resolution,[],[f300,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK1,sK2),X0)
        | ~ v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f207])).

fof(f301,plain,
    ( spl5_36
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f240,f196,f62,f299])).

fof(f240,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f234,f64])).

fof(f234,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_24 ),
    inference(superposition,[],[f46,f198])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f221,plain,
    ( ~ spl5_1
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl5_1
    | spl5_26 ),
    inference(subsumption_resolution,[],[f218,f59])).

fof(f218,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_26 ),
    inference(resolution,[],[f213,f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f213,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_26
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f214,plain,
    ( ~ spl5_26
    | ~ spl5_1
    | ~ spl5_12
    | spl5_23 ),
    inference(avatar_split_clause,[],[f205,f192,f126,f57,f211])).

fof(f126,plain,
    ( spl5_12
  <=> ! [X0] :
        ( m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f192,plain,
    ( spl5_23
  <=> m1_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f205,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ spl5_1
    | ~ spl5_12
    | spl5_23 ),
    inference(subsumption_resolution,[],[f204,f59])).

fof(f204,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | spl5_23 ),
    inference(resolution,[],[f194,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f194,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f192])).

fof(f209,plain,
    ( spl5_25
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f167,f161,f207])).

fof(f161,plain,
    ( spl5_18
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f167,plain,
    ( ! [X0] :
        ( v4_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_18 ),
    inference(resolution,[],[f163,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f163,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f199,plain,
    ( ~ spl5_23
    | spl5_24
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f190,f180,f153,f62,f196,f192])).

fof(f180,plain,
    ( spl5_21
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK0,X0)
        | u1_struct_0(X0) = u1_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f190,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f188,f64])).

fof(f188,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(resolution,[],[f181,f155])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(X0) = u1_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl5_21
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f177,f57,f180])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK0,X0)
        | u1_struct_0(X0) = u1_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f165,f59])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f164,plain,
    ( spl5_18
    | spl5_6
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f159,f149,f94,f83,f161])).

fof(f94,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f149,plain,
    ( spl5_16
  <=> ! [X1] :
        ( r2_hidden(sK4(sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | v2_tops_2(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f159,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | spl5_6
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f158,f85])).

fof(f158,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | v2_tops_2(sK2,sK1)
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(resolution,[],[f150,f96])).

fof(f96,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f150,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | r2_hidden(sK4(sK1,X1),X1)
        | v2_tops_2(X1,sK1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f156,plain,
    ( spl5_17
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f147,f136,f62,f153])).

fof(f136,plain,
    ( spl5_14
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f147,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f145,f64])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0)
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f137,f40])).

fof(f137,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X1,sK0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f151,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f119,f62,f149])).

fof(f119,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | v2_tops_2(X1,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f64])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f138,plain,
    ( spl5_14
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f134,f130,f111,f136])).

fof(f111,plain,
    ( spl5_10
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f130,plain,
    ( spl5_13
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f134,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X1,sK0) )
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(resolution,[],[f131,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X0,sK0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f131,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f109,f101,f62,f130])).

fof(f101,plain,
    ( spl5_9
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f109,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f108,f64])).

fof(f108,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_9 ),
    inference(superposition,[],[f41,f103])).

fof(f103,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f128,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f124,f115,f57,f126])).

fof(f115,plain,
    ( spl5_11
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f124,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f122,f59])).

fof(f122,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f116,f41])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f107,f101,f62,f115])).

fof(f107,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f106,f103])).

fof(f106,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f64])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f113,plain,
    ( spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f105,f57,f111])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X0,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f49,f59])).

fof(f104,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f36,f101])).

fof(f36,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X1)
                & v2_tops_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,sK1)
              & v2_tops_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,sK1)
            & v2_tops_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK1)
          & v2_tops_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK1)
        & v2_tops_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ v2_tops_2(sK3,sK1)
      & v2_tops_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).

fof(f97,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f92,f67,f94])).

fof(f67,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f35,f69])).

fof(f69,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f81,f77,f67,f83])).

fof(f77,plain,
    ( spl5_5
  <=> v2_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f81,plain,
    ( ~ v2_tops_2(sK2,sK1)
    | ~ spl5_3
    | spl5_5 ),
    inference(forward_demodulation,[],[f79,f69])).

fof(f79,plain,
    ( ~ v2_tops_2(sK3,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (1037)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (1037)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (1065)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (1055)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f86,f91,f97,f104,f113,f117,f128,f132,f138,f151,f156,f164,f182,f199,f209,f214,f221,f301,f314,f330,f336,f347,f354])).
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    ~spl5_2 | spl5_6 | ~spl5_7 | ~spl5_24 | ~spl5_41),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f353])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    $false | (~spl5_2 | spl5_6 | ~spl5_7 | ~spl5_24 | ~spl5_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f352,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_2 | spl5_6 | ~spl5_24 | ~spl5_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f351,f198])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f196])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl5_24 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_2 | spl5_6 | ~spl5_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f350,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    l1_pre_topc(sK1) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl5_2 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | (spl5_6 | ~spl5_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f348,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~v2_tops_2(sK2,sK1) | spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl5_6 <=> v2_tops_2(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    v2_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~spl5_41),
% 0.21/0.49    inference(resolution,[],[f346,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_pre_topc(sK4(X0,X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    v4_pre_topc(sK4(sK1,sK2),sK1) | ~spl5_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f344])).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    spl5_41 <=> v4_pre_topc(sK4(sK1,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    spl5_41 | ~spl5_17 | ~spl5_24 | ~spl5_39 | ~spl5_40),
% 0.21/0.49    inference(avatar_split_clause,[],[f342,f328,f324,f196,f153,f344])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl5_17 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    spl5_39 <=> m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    spl5_40 <=> ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v4_pre_topc(sK4(sK1,sK2),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    v4_pre_topc(sK4(sK1,sK2),sK1) | (~spl5_17 | ~spl5_24 | ~spl5_39 | ~spl5_40)),
% 0.21/0.49    inference(subsumption_resolution,[],[f341,f325])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f324])).
% 0.21/0.49  fof(f341,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK4(sK1,sK2),sK1) | (~spl5_17 | ~spl5_24 | ~spl5_40)),
% 0.21/0.49    inference(forward_demodulation,[],[f339,f198])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(sK4(sK1,sK2),sK1) | (~spl5_17 | ~spl5_40)),
% 0.21/0.49    inference(resolution,[],[f329,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0) | ~spl5_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f153])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(sK1,sK2),X0)) ) | ~spl5_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f328])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl5_6 | ~spl5_7 | ~spl5_36 | spl5_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f335])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    $false | (spl5_6 | ~spl5_7 | ~spl5_36 | spl5_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f334,f90])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl5_6 | ~spl5_36 | spl5_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f332,f85])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    v2_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_36 | spl5_39)),
% 0.21/0.49    inference(resolution,[],[f326,f300])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ( ! [X3] : (m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl5_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f299])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    spl5_36 <=> ! [X3] : (m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f324])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ~spl5_39 | spl5_40 | ~spl5_1 | ~spl5_37),
% 0.21/0.50    inference(avatar_split_clause,[],[f316,f311,f57,f328,f324])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    spl5_37 <=> v4_pre_topc(sK4(sK1,sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(sK1,sK2),X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_1 | ~spl5_37)),
% 0.21/0.50    inference(subsumption_resolution,[],[f315,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f57])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(sK1,sK2),X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl5_37),
% 0.21/0.50    inference(resolution,[],[f313,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    v4_pre_topc(sK4(sK1,sK2),sK0) | ~spl5_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f311])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    spl5_37 | ~spl5_1 | ~spl5_4 | spl5_6 | ~spl5_7 | ~spl5_25 | ~spl5_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f309,f299,f207,f88,f83,f72,f57,f311])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl5_4 <=> v2_tops_2(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl5_25 <=> ! [X0] : (v4_pre_topc(sK4(sK1,sK2),X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    v4_pre_topc(sK4(sK1,sK2),sK0) | (~spl5_1 | ~spl5_4 | spl5_6 | ~spl5_7 | ~spl5_25 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f308,f59])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    v4_pre_topc(sK4(sK1,sK2),sK0) | ~l1_pre_topc(sK0) | (~spl5_4 | spl5_6 | ~spl5_7 | ~spl5_25 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f307,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    v2_tops_2(sK2,sK0) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    v4_pre_topc(sK4(sK1,sK2),sK0) | ~v2_tops_2(sK2,sK0) | ~l1_pre_topc(sK0) | (spl5_6 | ~spl5_7 | ~spl5_25 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f306,f90])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK4(sK1,sK2),sK0) | ~v2_tops_2(sK2,sK0) | ~l1_pre_topc(sK0) | (spl5_6 | ~spl5_25 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f305,f85])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    v2_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK4(sK1,sK2),sK0) | ~v2_tops_2(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl5_25 | ~spl5_36)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f304])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    v2_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK4(sK1,sK2),sK0) | ~v2_tops_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (~spl5_25 | ~spl5_36)),
% 0.21/0.50    inference(resolution,[],[f300,f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(sK1,sK2),X0) | ~v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f207])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    spl5_36 | ~spl5_2 | ~spl5_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f240,f196,f62,f299])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ( ! [X3] : (m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl5_2 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f234,f64])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ( ! [X3] : (m1_subset_1(sK4(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1)) ) | ~spl5_24),
% 0.21/0.50    inference(superposition,[],[f46,f198])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ~spl5_1 | spl5_26),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    $false | (~spl5_1 | spl5_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f59])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | spl5_26),
% 0.21/0.50    inference(resolution,[],[f213,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ~m1_pre_topc(sK0,sK0) | spl5_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f211])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    spl5_26 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ~spl5_26 | ~spl5_1 | ~spl5_12 | spl5_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f205,f192,f126,f57,f211])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl5_12 <=> ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl5_23 <=> m1_pre_topc(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~m1_pre_topc(sK0,sK0) | (~spl5_1 | ~spl5_12 | spl5_23)),
% 0.21/0.50    inference(subsumption_resolution,[],[f204,f59])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | (~spl5_12 | spl5_23)),
% 0.21/0.50    inference(resolution,[],[f194,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X0)) ) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ~m1_pre_topc(sK0,sK1) | spl5_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f192])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    spl5_25 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f167,f161,f207])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl5_18 <=> r2_hidden(sK4(sK1,sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (v4_pre_topc(sK4(sK1,sK2),X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_18),
% 0.21/0.50    inference(resolution,[],[f163,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,sK2),sK2) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f161])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~spl5_23 | spl5_24 | ~spl5_2 | ~spl5_17 | ~spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f190,f180,f153,f62,f196,f192])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl5_21 <=> ! [X0] : (~m1_pre_topc(sK0,X0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(sK1) | ~m1_pre_topc(sK0,sK1) | (~spl5_2 | ~spl5_17 | ~spl5_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f64])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(sK1) | ~m1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK1) | (~spl5_17 | ~spl5_21)),
% 0.21/0.50    inference(resolution,[],[f181,f155])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0)) ) | ~spl5_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f180])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl5_21 | ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f177,f57,f180])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK0,X0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X0)) ) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f165,f59])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(resolution,[],[f99,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 0.21/0.50    inference(resolution,[],[f43,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl5_18 | spl5_6 | ~spl5_8 | ~spl5_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f159,f149,f94,f83,f161])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl5_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl5_16 <=> ! [X1] : (r2_hidden(sK4(sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_2(X1,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,sK2),sK2) | (spl5_6 | ~spl5_8 | ~spl5_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f85])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,sK2),sK2) | v2_tops_2(sK2,sK1) | (~spl5_8 | ~spl5_16)),
% 0.21/0.50    inference(resolution,[],[f150,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(sK4(sK1,X1),X1) | v2_tops_2(X1,sK1)) ) | ~spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl5_17 | ~spl5_2 | ~spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f147,f136,f62,f153])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl5_14 <=> ! [X1] : (~m1_pre_topc(X1,sK1) | ~l1_pre_topc(X1) | m1_pre_topc(X1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK0) | (~spl5_2 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f145,f64])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0) | ~spl5_14),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK1) | ~spl5_14),
% 0.21/0.50    inference(resolution,[],[f137,f40])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_pre_topc(X1,sK1) | ~l1_pre_topc(X1) | m1_pre_topc(X1,sK0)) ) | ~spl5_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl5_16 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f119,f62,f149])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK4(sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_2(X1,sK1)) ) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f47,f64])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl5_14 | ~spl5_10 | ~spl5_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f130,f111,f136])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl5_10 <=> ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl5_13 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_pre_topc(X1,sK1) | ~l1_pre_topc(X1) | m1_pre_topc(X1,sK0)) ) | (~spl5_10 | ~spl5_13)),
% 0.21/0.50    inference(resolution,[],[f131,f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK0)) ) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f111])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f130])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl5_13 | ~spl5_2 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f109,f101,f62,f130])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl5_9 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | (~spl5_2 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f64])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl5_9),
% 0.21/0.50    inference(superposition,[],[f41,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl5_12 | ~spl5_1 | ~spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f124,f115,f57,f126])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl5_11 <=> ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X0)) ) | (~spl5_1 | ~spl5_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f59])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0)) ) | ~spl5_11),
% 0.21/0.50    inference(resolution,[],[f116,f41])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK1)) ) | ~spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl5_11 | ~spl5_2 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f107,f101,f62,f115])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK1)) ) | (~spl5_2 | ~spl5_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f106,f103])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1)) ) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f49,f64])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl5_10 | ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f57,f111])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK0)) ) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f49,f59])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f101])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    (((~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tops_2(X3,X1) & (v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl5_8 | ~spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f92,f67,f94])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl5_3 <=> sK2 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl5_3),
% 0.21/0.50    inference(forward_demodulation,[],[f35,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    sK2 = sK3 | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f88])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_3 | spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f81,f77,f67,f83])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl5_5 <=> v2_tops_2(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~v2_tops_2(sK2,sK1) | (~spl5_3 | spl5_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f79,f69])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~v2_tops_2(sK3,sK1) | spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f77])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~v2_tops_2(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f72])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v2_tops_2(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f67])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    sK2 = sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f62])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f57])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1037)------------------------------
% 0.21/0.50  % (1037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1037)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1037)Memory used [KB]: 6396
% 0.21/0.50  % (1037)Time elapsed: 0.069 s
% 0.21/0.50  % (1037)------------------------------
% 0.21/0.50  % (1037)------------------------------
% 0.21/0.50  % (1031)Success in time 0.137 s
%------------------------------------------------------------------------------
