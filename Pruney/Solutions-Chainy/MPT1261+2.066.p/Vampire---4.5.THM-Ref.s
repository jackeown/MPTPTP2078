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
% DateTime   : Thu Dec  3 13:11:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 311 expanded)
%              Number of leaves         :   43 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :  515 (1039 expanded)
%              Number of equality atoms :  129 ( 271 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f76,f85,f91,f98,f111,f115,f125,f153,f181,f186,f195,f205,f209,f218,f260,f275,f281,f294,f307,f316,f326,f331,f355,f368,f378,f385])).

fof(f385,plain,
    ( ~ spl2_3
    | spl2_5
    | ~ spl2_32
    | ~ spl2_37
    | ~ spl2_40 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl2_3
    | spl2_5
    | ~ spl2_32
    | ~ spl2_37
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f334,f383])).

fof(f383,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | spl2_5
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f282,f79])).

fof(f79,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f282,plain,
    ( v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(resolution,[],[f280,f71])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) != X0 )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl2_32
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f334,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_37
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f332,f315])).

fof(f315,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl2_37
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f332,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_40 ),
    inference(resolution,[],[f330,f71])).

fof(f330,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl2_40
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f378,plain,
    ( ~ spl2_3
    | ~ spl2_29
    | ~ spl2_32
    | ~ spl2_46 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_32
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f371,f376])).

fof(f376,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f38,f375])).

fof(f375,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f282,f259])).

fof(f259,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl2_29
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f38,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
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
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f371,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f369,f259])).

fof(f369,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(resolution,[],[f367,f71])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl2_46
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f368,plain,
    ( spl2_46
    | ~ spl2_2
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f364,f353,f64,f366])).

fof(f64,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f353,plain,
    ( spl2_44
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_44 ),
    inference(resolution,[],[f354,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f353])).

fof(f355,plain,(
    spl2_44 ),
    inference(avatar_split_clause,[],[f40,f353])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f331,plain,
    ( spl2_40
    | ~ spl2_2
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f327,f324,f64,f329])).

fof(f324,plain,
    ( spl2_39
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_39 ),
    inference(resolution,[],[f325,f66])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f324])).

fof(f326,plain,(
    spl2_39 ),
    inference(avatar_split_clause,[],[f39,f324])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f316,plain,
    ( spl2_37
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f310,f305,f215,f69,f313])).

fof(f215,plain,
    ( spl2_24
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f305,plain,
    ( spl2_36
  <=> ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f310,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f308,f217])).

fof(f217,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f215])).

fof(f308,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_36 ),
    inference(resolution,[],[f306,f71])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f305])).

fof(f307,plain,
    ( spl2_36
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f298,f292,f109,f64,f305])).

fof(f109,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f292,plain,
    ( spl2_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f298,plain,
    ( ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f296,f66])).

fof(f296,plain,
    ( ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_10
    | ~ spl2_34 ),
    inference(resolution,[],[f293,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f289,f273,f69,f292])).

fof(f273,plain,
    ( spl2_31
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) )
    | ~ spl2_3
    | ~ spl2_31 ),
    inference(resolution,[],[f274,f71])).

fof(f274,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f273])).

fof(f281,plain,
    ( spl2_32
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f277,f207,f64,f59,f279])).

fof(f59,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f207,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f277,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f276,f66])).

fof(f276,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f208,f61])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f275,plain,(
    spl2_31 ),
    inference(avatar_split_clause,[],[f57,f273])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f260,plain,
    ( spl2_29
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f255,f184,f78,f69,f257])).

fof(f184,plain,
    ( spl2_20
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f255,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f254,f71])).

fof(f254,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(resolution,[],[f80,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f80,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f218,plain,
    ( spl2_24
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f210,f203,f82,f215])).

fof(f82,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f203,plain,
    ( spl2_22
  <=> ! [X0] : sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f210,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(superposition,[],[f204,f84])).

fof(f84,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f204,plain,
    ( ! [X0] : sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f209,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f42,f207])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f205,plain,
    ( spl2_22
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f198,f193,f151,f203])).

fof(f151,plain,
    ( spl2_16
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f193,plain,
    ( spl2_21
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f198,plain,
    ( ! [X0] : sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(superposition,[],[f152,f194])).

fof(f194,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f152,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f195,plain,
    ( spl2_21
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f190,f179,f69,f193])).

fof(f179,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f190,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(resolution,[],[f180,f71])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f186,plain,
    ( spl2_20
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f182,f123,f64,f184])).

fof(f123,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(resolution,[],[f124,f66])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f181,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f56,f179])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f153,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f120,f113,f96,f74,f151])).

fof(f74,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f96,plain,
    ( spl2_8
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f113,plain,
    ( spl2_11
  <=> ! [X1,X0] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f120,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f118,f75])).

fof(f75,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f118,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = X0
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(superposition,[],[f97,f114])).

fof(f114,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f97,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f125,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f41,f123])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f55,f113])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f48,f45,f44,f53])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f111,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f50,f109])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f98,plain,
    ( spl2_8
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f92,f89,f74,f96])).

fof(f89,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f92,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f90,f75])).

fof(f90,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f54,f89])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f45,f45,f45])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f85,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f37,f82,f78])).

fof(f37,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f72,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f36,f69])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (25740)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (25740)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f386,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f62,f67,f72,f76,f85,f91,f98,f111,f115,f125,f153,f181,f186,f195,f205,f209,f218,f260,f275,f281,f294,f307,f316,f326,f331,f355,f368,f378,f385])).
% 0.21/0.44  fof(f385,plain,(
% 0.21/0.44    ~spl2_3 | spl2_5 | ~spl2_32 | ~spl2_37 | ~spl2_40),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.44  fof(f384,plain,(
% 0.21/0.44    $false | (~spl2_3 | spl2_5 | ~spl2_32 | ~spl2_37 | ~spl2_40)),
% 0.21/0.44    inference(subsumption_resolution,[],[f334,f383])).
% 0.21/0.44  fof(f383,plain,(
% 0.21/0.44    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_3 | spl2_5 | ~spl2_32)),
% 0.21/0.44    inference(subsumption_resolution,[],[f282,f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f282,plain,(
% 0.21/0.44    v4_pre_topc(sK1,sK0) | sK1 != k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_32)),
% 0.21/0.44    inference(resolution,[],[f280,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f280,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) != X0) ) | ~spl2_32),
% 0.21/0.44    inference(avatar_component_clause,[],[f279])).
% 0.21/0.44  fof(f279,plain,(
% 0.21/0.44    spl2_32 <=> ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.44  fof(f334,plain,(
% 0.21/0.44    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_37 | ~spl2_40)),
% 0.21/0.44    inference(forward_demodulation,[],[f332,f315])).
% 0.21/0.44  fof(f315,plain,(
% 0.21/0.44    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.21/0.44    inference(avatar_component_clause,[],[f313])).
% 0.21/0.44  fof(f313,plain,(
% 0.21/0.44    spl2_37 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.44  fof(f332,plain,(
% 0.21/0.44    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_40)),
% 0.21/0.44    inference(resolution,[],[f330,f71])).
% 0.21/0.44  fof(f330,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_40),
% 0.21/0.44    inference(avatar_component_clause,[],[f329])).
% 0.21/0.44  fof(f329,plain,(
% 0.21/0.44    spl2_40 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.44  fof(f378,plain,(
% 0.21/0.44    ~spl2_3 | ~spl2_29 | ~spl2_32 | ~spl2_46),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f377])).
% 0.21/0.44  fof(f377,plain,(
% 0.21/0.44    $false | (~spl2_3 | ~spl2_29 | ~spl2_32 | ~spl2_46)),
% 0.21/0.44    inference(subsumption_resolution,[],[f371,f376])).
% 0.21/0.44  fof(f376,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_29 | ~spl2_32)),
% 0.21/0.44    inference(subsumption_resolution,[],[f38,f375])).
% 0.21/0.44  fof(f375,plain,(
% 0.21/0.44    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_29 | ~spl2_32)),
% 0.21/0.44    inference(subsumption_resolution,[],[f282,f259])).
% 0.21/0.44  fof(f259,plain,(
% 0.21/0.44    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f257])).
% 0.21/0.44  fof(f257,plain,(
% 0.21/0.44    spl2_29 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f14])).
% 0.21/0.44  fof(f14,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.44  fof(f371,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_29 | ~spl2_46)),
% 0.21/0.44    inference(forward_demodulation,[],[f369,f259])).
% 0.21/0.44  fof(f369,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_46)),
% 0.21/0.44    inference(resolution,[],[f367,f71])).
% 0.21/0.44  fof(f367,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_46),
% 0.21/0.44    inference(avatar_component_clause,[],[f366])).
% 0.21/0.44  fof(f366,plain,(
% 0.21/0.44    spl2_46 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.21/0.44  fof(f368,plain,(
% 0.21/0.44    spl2_46 | ~spl2_2 | ~spl2_44),
% 0.21/0.44    inference(avatar_split_clause,[],[f364,f353,f64,f366])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f353,plain,(
% 0.21/0.44    spl2_44 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.44  fof(f364,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_44)),
% 0.21/0.44    inference(resolution,[],[f354,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f354,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_44),
% 0.21/0.44    inference(avatar_component_clause,[],[f353])).
% 0.21/0.44  fof(f355,plain,(
% 0.21/0.44    spl2_44),
% 0.21/0.44    inference(avatar_split_clause,[],[f40,f353])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.44  fof(f331,plain,(
% 0.21/0.44    spl2_40 | ~spl2_2 | ~spl2_39),
% 0.21/0.44    inference(avatar_split_clause,[],[f327,f324,f64,f329])).
% 0.21/0.44  fof(f324,plain,(
% 0.21/0.44    spl2_39 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.44  fof(f327,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_39)),
% 0.21/0.44    inference(resolution,[],[f325,f66])).
% 0.21/0.44  fof(f325,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_39),
% 0.21/0.44    inference(avatar_component_clause,[],[f324])).
% 0.21/0.44  fof(f326,plain,(
% 0.21/0.44    spl2_39),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f324])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.44  fof(f316,plain,(
% 0.21/0.44    spl2_37 | ~spl2_3 | ~spl2_24 | ~spl2_36),
% 0.21/0.44    inference(avatar_split_clause,[],[f310,f305,f215,f69,f313])).
% 0.21/0.44  fof(f215,plain,(
% 0.21/0.44    spl2_24 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.44  fof(f305,plain,(
% 0.21/0.44    spl2_36 <=> ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.44  fof(f310,plain,(
% 0.21/0.44    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_24 | ~spl2_36)),
% 0.21/0.44    inference(forward_demodulation,[],[f308,f217])).
% 0.21/0.44  fof(f217,plain,(
% 0.21/0.44    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f215])).
% 0.21/0.44  fof(f308,plain,(
% 0.21/0.44    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_36)),
% 0.21/0.44    inference(resolution,[],[f306,f71])).
% 0.21/0.44  fof(f306,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))) ) | ~spl2_36),
% 0.21/0.44    inference(avatar_component_clause,[],[f305])).
% 0.21/0.44  fof(f307,plain,(
% 0.21/0.44    spl2_36 | ~spl2_2 | ~spl2_10 | ~spl2_34),
% 0.21/0.44    inference(avatar_split_clause,[],[f298,f292,f109,f64,f305])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl2_10 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f292,plain,(
% 0.21/0.44    spl2_34 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.44  fof(f298,plain,(
% 0.21/0.44    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_10 | ~spl2_34)),
% 0.21/0.44    inference(subsumption_resolution,[],[f296,f66])).
% 0.21/0.44  fof(f296,plain,(
% 0.21/0.44    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_10 | ~spl2_34)),
% 0.21/0.44    inference(resolution,[],[f293,f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f109])).
% 0.21/0.44  fof(f293,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))) ) | ~spl2_34),
% 0.21/0.44    inference(avatar_component_clause,[],[f292])).
% 0.21/0.44  fof(f294,plain,(
% 0.21/0.44    spl2_34 | ~spl2_3 | ~spl2_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f289,f273,f69,f292])).
% 0.21/0.44  fof(f273,plain,(
% 0.21/0.44    spl2_31 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.44  fof(f289,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))) ) | (~spl2_3 | ~spl2_31)),
% 0.21/0.44    inference(resolution,[],[f274,f71])).
% 0.21/0.44  fof(f274,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) ) | ~spl2_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f273])).
% 0.21/0.45  fof(f281,plain,(
% 0.21/0.45    spl2_32 | ~spl2_1 | ~spl2_2 | ~spl2_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f277,f207,f64,f59,f279])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    spl2_23 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.45  fof(f277,plain,(
% 0.21/0.45    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f276,f66])).
% 0.21/0.45  fof(f276,plain,(
% 0.21/0.45    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_1 | ~spl2_23)),
% 0.21/0.45    inference(resolution,[],[f208,f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f207])).
% 0.21/0.45  fof(f275,plain,(
% 0.21/0.45    spl2_31),
% 0.21/0.45    inference(avatar_split_clause,[],[f57,f273])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f52,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(flattening,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.45  fof(f260,plain,(
% 0.21/0.45    spl2_29 | ~spl2_3 | ~spl2_5 | ~spl2_20),
% 0.21/0.45    inference(avatar_split_clause,[],[f255,f184,f78,f69,f257])).
% 0.21/0.45  fof(f184,plain,(
% 0.21/0.45    spl2_20 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.45  fof(f255,plain,(
% 0.21/0.45    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_5 | ~spl2_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f254,f71])).
% 0.21/0.45  fof(f254,plain,(
% 0.21/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_5 | ~spl2_20)),
% 0.21/0.45    inference(resolution,[],[f80,f185])).
% 0.21/0.45  fof(f185,plain,(
% 0.21/0.45    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f184])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f218,plain,(
% 0.21/0.45    spl2_24 | ~spl2_6 | ~spl2_22),
% 0.21/0.45    inference(avatar_split_clause,[],[f210,f203,f82,f215])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    spl2_22 <=> ! [X0] : sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_6 | ~spl2_22)),
% 0.21/0.45    inference(superposition,[],[f204,f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f82])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    ( ! [X0] : (sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ) | ~spl2_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f203])).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    spl2_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f42,f207])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    spl2_22 | ~spl2_16 | ~spl2_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f198,f193,f151,f203])).
% 0.21/0.45  fof(f151,plain,(
% 0.21/0.45    spl2_16 <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.45  fof(f193,plain,(
% 0.21/0.45    spl2_21 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    ( ! [X0] : (sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ) | (~spl2_16 | ~spl2_21)),
% 0.21/0.45    inference(superposition,[],[f152,f194])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f193])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) ) | ~spl2_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f151])).
% 0.21/0.45  fof(f195,plain,(
% 0.21/0.45    spl2_21 | ~spl2_3 | ~spl2_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f190,f179,f69,f193])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    spl2_19 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.45  fof(f190,plain,(
% 0.21/0.45    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | (~spl2_3 | ~spl2_19)),
% 0.21/0.45    inference(resolution,[],[f180,f71])).
% 0.21/0.45  fof(f180,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ) | ~spl2_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f179])).
% 0.21/0.45  fof(f186,plain,(
% 0.21/0.45    spl2_20 | ~spl2_2 | ~spl2_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f182,f123,f64,f184])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    spl2_12 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.45  fof(f182,plain,(
% 0.21/0.45    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_12)),
% 0.21/0.45    inference(resolution,[],[f124,f66])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f123])).
% 0.21/0.45  fof(f181,plain,(
% 0.21/0.45    spl2_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f56,f179])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f51,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f46,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    spl2_16 | ~spl2_4 | ~spl2_8 | ~spl2_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f120,f113,f96,f74,f151])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl2_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl2_8 <=> ! [X1,X0] : k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    spl2_11 <=> ! [X1,X0] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) ) | (~spl2_4 | ~spl2_8 | ~spl2_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f118,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f74])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = X0) ) | (~spl2_8 | ~spl2_11)),
% 0.21/0.45    inference(superposition,[],[f97,f114])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) ) | ~spl2_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f113])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))) ) | ~spl2_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f96])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    spl2_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f41,f123])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    spl2_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f55,f113])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f48,f45,f44,f53])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    spl2_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f50,f109])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl2_8 | ~spl2_4 | ~spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f92,f89,f74,f96])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl2_7 <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.45    inference(superposition,[],[f90,f75])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) ) | ~spl2_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f89])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f54,f89])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f47,f45,f45,f45])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl2_5 | spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f82,f78])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f43,f74])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f36,f69])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f35,f64])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f34,f59])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    v2_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (25740)------------------------------
% 0.21/0.45  % (25740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (25740)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (25740)Memory used [KB]: 6396
% 0.21/0.45  % (25740)Time elapsed: 0.017 s
% 0.21/0.45  % (25740)------------------------------
% 0.21/0.45  % (25740)------------------------------
% 0.21/0.45  % (25732)Success in time 0.088 s
%------------------------------------------------------------------------------
