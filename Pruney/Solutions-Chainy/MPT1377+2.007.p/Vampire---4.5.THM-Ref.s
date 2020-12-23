%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 452 expanded)
%              Number of leaves         :   35 ( 183 expanded)
%              Depth                    :   15
%              Number of atoms          :  764 (1948 expanded)
%              Number of equality atoms :   69 ( 167 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f79,f92,f96,f105,f116,f123,f136,f172,f211,f260,f274,f281,f335,f414,f425,f458,f530,f571,f580,f581,f594,f623,f636,f638])).

fof(f638,plain,
    ( u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f636,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5
    | spl2_28
    | ~ spl2_29 ),
    inference(avatar_contradiction_clause,[],[f635])).

fof(f635,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5
    | spl2_28
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f632,f413])).

fof(f413,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl2_29
  <=> v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f632,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5
    | spl2_28 ),
    inference(unit_resulting_resolution,[],[f69,f64,f73,f84,f408,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X0,X1))
      | v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(f408,plain,
    ( k1_xboole_0 != sK1
    | spl2_28 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl2_28
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f73,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_3
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (10498)Refutation not found, incomplete strategy% (10498)------------------------------
% (10498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10498)Termination reason: Refutation not found, incomplete strategy

% (10498)Memory used [KB]: 10618
% (10498)Time elapsed: 0.084 s
% (10498)------------------------------
% (10498)------------------------------
fof(f623,plain,
    ( ~ spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_30
    | spl2_32
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_30
    | spl2_32
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f600,f621])).

fof(f621,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_30
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(forward_demodulation,[],[f620,f429])).

fof(f429,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl2_30
  <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f620,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f619,f562])).

fof(f562,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl2_41
  <=> v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f619,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f236,f529])).

fof(f529,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl2_39
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f236,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f230,f135])).

fof(f135,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl2_10
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f230,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_15 ),
    inference(superposition,[],[f59,f210])).

fof(f210,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl2_15
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f600,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_2
    | spl2_32
    | ~ spl2_39 ),
    inference(unit_resulting_resolution,[],[f69,f529,f456,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | v2_compts_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f456,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | spl2_32 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl2_32
  <=> v2_compts_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f594,plain,
    ( ~ spl2_32
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_28
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f590,f561,f407,f87,f82,f455])).

fof(f87,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f590,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_28
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f583,f562])).

fof(f583,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f582,f409])).

fof(f409,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f407])).

fof(f582,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f419,f409])).

fof(f419,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f418,f84])).

fof(f418,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f41,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f41,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v2_compts_1(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_compts_1(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_compts_1(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

fof(f581,plain,
    ( k1_xboole_0 != sK1
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f580,plain,
    ( ~ spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_30
    | ~ spl2_32
    | ~ spl2_39
    | spl2_41 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_30
    | ~ spl2_32
    | ~ spl2_39
    | spl2_41 ),
    inference(subsumption_resolution,[],[f578,f529])).

fof(f578,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_30
    | ~ spl2_32
    | ~ spl2_39
    | spl2_41 ),
    inference(forward_demodulation,[],[f577,f210])).

fof(f577,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_30
    | ~ spl2_32
    | ~ spl2_39
    | spl2_41 ),
    inference(subsumption_resolution,[],[f576,f135])).

fof(f576,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2
    | ~ spl2_30
    | ~ spl2_32
    | ~ spl2_39
    | spl2_41 ),
    inference(subsumption_resolution,[],[f575,f563])).

fof(f563,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_41 ),
    inference(avatar_component_clause,[],[f561])).

fof(f575,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2
    | ~ spl2_30
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f573,f536])).

fof(f536,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(unit_resulting_resolution,[],[f69,f457,f529,f59])).

fof(f457,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f455])).

fof(f573,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_30 ),
    inference(superposition,[],[f58,f429])).

fof(f571,plain,
    ( spl2_30
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f443,f407,f297,f427])).

fof(f297,plain,
    ( spl2_22
  <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f443,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(superposition,[],[f299,f409])).

fof(f299,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f297])).

fof(f530,plain,
    ( spl2_39
    | ~ spl2_5
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f436,f407,f82,f527])).

fof(f436,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_28 ),
    inference(superposition,[],[f84,f409])).

fof(f458,plain,
    ( spl2_32
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f434,f407,f72,f455])).

fof(f434,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(superposition,[],[f74,f409])).

fof(f74,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f425,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f424,f297,f133,f113,f87,f82,f76,f72,f67,f62,f407])).

fof(f76,plain,
    ( spl2_4
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f113,plain,
    ( spl2_8
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f424,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f423,f420])).

fof(f420,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f417,f77])).

fof(f77,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f417,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK1
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f416,f135])).

fof(f416,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK1
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f415,f89])).

fof(f415,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f373,f115])).

fof(f115,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f373,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_22 ),
    inference(superposition,[],[f48,f299])).

fof(f423,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f422,f84])).

fof(f422,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f74,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_compts_1(k1_pre_topc(sK0,X0)) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f110,f64])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | k1_xboole_0 = X0
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_compts_1(k1_pre_topc(sK0,X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f47,f69])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_compts_1(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f414,plain,
    ( spl2_28
    | spl2_29
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f402,f297,f133,f113,f87,f76,f411,f407])).

fof(f402,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f401,f299])).

fof(f401,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f400,f89])).

fof(f400,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f167,f78])).

fof(f78,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f167,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) )
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f153,f115])).

fof(f153,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | k1_xboole_0 = X1
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) )
    | ~ spl2_10 ),
    inference(resolution,[],[f135,f47])).

fof(f335,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f284,f278,f271,f87,f82,f67,f297])).

fof(f271,plain,
    ( spl2_18
  <=> v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f278,plain,
    ( spl2_19
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f284,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f276,f282])).

fof(f282,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f69,f280,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f280,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f278])).

fof(f276,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f275,f264])).

fof(f264,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f69,f89,f84,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

fof(f275,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_18 ),
    inference(resolution,[],[f273,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f273,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f271])).

fof(f281,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f265,f82,f67,f278])).

fof(f265,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f69,f84,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f274,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f266,f82,f67,f271])).

fof(f266,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f69,f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f260,plain,
    ( spl2_5
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f228,f208,f87,f82])).

fof(f228,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(superposition,[],[f89,f210])).

fof(f211,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f174,f169,f120,f208])).

fof(f120,plain,
    ( spl2_9
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f169,plain,
    ( spl2_11
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f174,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f122,f171,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f171,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f122,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f172,plain,
    ( spl2_11
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f128,f120,f102,f169])).

fof(f102,plain,
    ( spl2_7
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f128,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f118,f124])).

fof(f124,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f122,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f118,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_7 ),
    inference(resolution,[],[f104,f43])).

fof(f104,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f136,plain,
    ( spl2_10
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f124,f120,f133])).

fof(f123,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f93,f67,f120])).

fof(f93,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f116,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f98,f67,f62,f113])).

fof(f98,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f105,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f97,f67,f62,f102])).

fof(f97,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f40,f87,f82])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,
    ( ~ spl2_3
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f91,f87,f76,f82,f72])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f80,f89])).

fof(f80,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f41,f78])).

fof(f79,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f37,f76,f72])).

fof(f37,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (10521)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.48  % (10513)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (10498)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (10521)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f639,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f65,f70,f79,f92,f96,f105,f116,f123,f136,f172,f211,f260,f274,f281,f335,f414,f425,f458,f530,f571,f580,f581,f594,f623,f636,f638])).
% 0.21/0.50  fof(f638,plain,(
% 0.21/0.50    u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f636,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5 | spl2_28 | ~spl2_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f635])).
% 0.21/0.50  fof(f635,plain,(
% 0.21/0.50    $false | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5 | spl2_28 | ~spl2_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f632,f413])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(sK0,sK1)) | ~spl2_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f411])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    spl2_29 <=> v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5 | spl2_28)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f69,f64,f73,f84,f408,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl2_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f407])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    spl2_28 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~v2_compts_1(sK1,sK0) | spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl2_3 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  % (10498)Refutation not found, incomplete strategy% (10498)------------------------------
% 0.21/0.50  % (10498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10498)Memory used [KB]: 10618
% 0.21/0.50  % (10498)Time elapsed: 0.084 s
% 0.21/0.50  % (10498)------------------------------
% 0.21/0.50  % (10498)------------------------------
% 0.21/0.50  fof(f623,plain,(
% 0.21/0.50    ~spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_30 | spl2_32 | ~spl2_39 | ~spl2_41),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f622])).
% 0.21/0.50  fof(f622,plain,(
% 0.21/0.50    $false | (~spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_30 | spl2_32 | ~spl2_39 | ~spl2_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f600,f621])).
% 0.21/0.50  fof(f621,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_10 | ~spl2_15 | ~spl2_30 | ~spl2_39 | ~spl2_41)),
% 0.21/0.50    inference(forward_demodulation,[],[f620,f429])).
% 0.21/0.50  fof(f429,plain,(
% 0.21/0.50    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) | ~spl2_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f427])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    spl2_30 <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.50  fof(f620,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | (~spl2_10 | ~spl2_15 | ~spl2_39 | ~spl2_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f619,f562])).
% 0.21/0.50  fof(f562,plain,(
% 0.21/0.50    v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f561])).
% 0.21/0.50  fof(f561,plain,(
% 0.21/0.50    spl2_41 <=> v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.50  fof(f619,plain,(
% 0.21/0.50    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | (~spl2_10 | ~spl2_15 | ~spl2_39)),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f529])).
% 0.21/0.50  fof(f529,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f527])).
% 0.21/0.50  fof(f527,plain,(
% 0.21/0.50    spl2_39 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | (~spl2_10 | ~spl2_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f230,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl2_10 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_15),
% 0.21/0.50    inference(superposition,[],[f59,f210])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    spl2_15 <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(k1_xboole_0,X0) | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_2 | spl2_32 | ~spl2_39)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f69,f529,f456,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f456,plain,(
% 0.21/0.50    ~v2_compts_1(k1_xboole_0,sK0) | spl2_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f455])).
% 0.21/0.50  fof(f455,plain,(
% 0.21/0.50    spl2_32 <=> v2_compts_1(k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    ~spl2_32 | ~spl2_5 | ~spl2_6 | ~spl2_28 | ~spl2_41),
% 0.21/0.50    inference(avatar_split_clause,[],[f590,f561,f407,f87,f82,f455])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.50  fof(f590,plain,(
% 0.21/0.50    ~v2_compts_1(k1_xboole_0,sK0) | (~spl2_5 | ~spl2_6 | ~spl2_28 | ~spl2_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f583,f562])).
% 0.21/0.50  fof(f583,plain,(
% 0.21/0.50    ~v2_compts_1(k1_xboole_0,sK0) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_5 | ~spl2_6 | ~spl2_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f582,f409])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl2_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f407])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_compts_1(sK1,sK0) | (~spl2_5 | ~spl2_6 | ~spl2_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f419,f409])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_compts_1(sK1,sK0) | (~spl2_5 | ~spl2_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f418,f84])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | ~spl2_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f41,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).
% 0.21/0.50  fof(f581,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f580,plain,(
% 0.21/0.50    ~spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_30 | ~spl2_32 | ~spl2_39 | spl2_41),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f579])).
% 0.21/0.50  fof(f579,plain,(
% 0.21/0.50    $false | (~spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_30 | ~spl2_32 | ~spl2_39 | spl2_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f578,f529])).
% 0.21/0.50  fof(f578,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_30 | ~spl2_32 | ~spl2_39 | spl2_41)),
% 0.21/0.50    inference(forward_demodulation,[],[f577,f210])).
% 0.21/0.50  fof(f577,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | (~spl2_2 | ~spl2_10 | ~spl2_30 | ~spl2_32 | ~spl2_39 | spl2_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f576,f135])).
% 0.21/0.50  fof(f576,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_2 | ~spl2_30 | ~spl2_32 | ~spl2_39 | spl2_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f575,f563])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f561])).
% 0.21/0.50  fof(f575,plain,(
% 0.21/0.50    v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_2 | ~spl2_30 | ~spl2_32 | ~spl2_39)),
% 0.21/0.50    inference(subsumption_resolution,[],[f573,f536])).
% 0.21/0.50  fof(f536,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_2 | ~spl2_32 | ~spl2_39)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f69,f457,f529,f59])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    v2_compts_1(k1_xboole_0,sK0) | ~spl2_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f455])).
% 0.21/0.50  fof(f573,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_30),
% 0.21/0.50    inference(superposition,[],[f58,f429])).
% 0.21/0.50  fof(f571,plain,(
% 0.21/0.50    spl2_30 | ~spl2_22 | ~spl2_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f443,f407,f297,f427])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    spl2_22 <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.50  fof(f443,plain,(
% 0.21/0.50    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) | (~spl2_22 | ~spl2_28)),
% 0.21/0.50    inference(superposition,[],[f299,f409])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~spl2_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f297])).
% 0.21/0.50  fof(f530,plain,(
% 0.21/0.50    spl2_39 | ~spl2_5 | ~spl2_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f436,f407,f82,f527])).
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_28)),
% 0.21/0.50    inference(superposition,[],[f84,f409])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    spl2_32 | ~spl2_3 | ~spl2_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f434,f407,f72,f455])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    v2_compts_1(k1_xboole_0,sK0) | (~spl2_3 | ~spl2_28)),
% 0.21/0.50    inference(superposition,[],[f74,f409])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    v2_compts_1(sK1,sK0) | ~spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_10 | ~spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f424,f297,f133,f113,f87,f82,f76,f72,f67,f62,f407])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl2_4 <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl2_8 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_10 | ~spl2_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f423,f420])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK1 | (spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_10 | ~spl2_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f417,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = sK1 | (~spl2_6 | ~spl2_8 | ~spl2_10 | ~spl2_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f416,f135])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = sK1 | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_6 | ~spl2_8 | ~spl2_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f415,f89])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_8 | ~spl2_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f373,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_22),
% 0.21/0.50    inference(superposition,[],[f48,f299])).
% 0.21/0.50  fof(f423,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f422,f84])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.50    inference(resolution,[],[f74,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_compts_1(X0,sK0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_compts_1(k1_pre_topc(sK0,X0))) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f64])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_compts_1(X0,sK0) | k1_xboole_0 = X0 | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_compts_1(k1_pre_topc(sK0,X0))) ) | ~spl2_2),
% 0.21/0.50    inference(resolution,[],[f47,f69])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_compts_1(k1_pre_topc(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    spl2_28 | spl2_29 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_10 | ~spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f402,f297,f133,f113,f87,f76,f411,f407])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK1 | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_10 | ~spl2_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f401,f299])).
% 0.21/0.50  fof(f401,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f400,f89])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | (~spl2_4 | ~spl2_8 | ~spl2_10)),
% 0.21/0.50    inference(resolution,[],[f167,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X1] : (~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1))) ) | (~spl2_8 | ~spl2_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f153,f115])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X1] : (~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = X1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1))) ) | ~spl2_10),
% 0.21/0.50    inference(resolution,[],[f135,f47])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl2_22 | ~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_18 | ~spl2_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f284,f278,f271,f87,f82,f67,f297])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl2_18 <=> v1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    spl2_19 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_18 | ~spl2_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f276,f282])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_19)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f69,f280,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl2_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f278])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_18)),
% 0.21/0.51    inference(forward_demodulation,[],[f275,f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | (~spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f69,f89,f84,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_18),
% 0.21/0.51    inference(resolution,[],[f273,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f271])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    spl2_19 | ~spl2_2 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f265,f82,f67,f278])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl2_2 | ~spl2_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f69,f84,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    spl2_18 | ~spl2_2 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f266,f82,f67,f271])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    v1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f69,f84,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    spl2_5 | ~spl2_6 | ~spl2_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f228,f208,f87,f82])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_6 | ~spl2_15)),
% 0.21/0.51    inference(superposition,[],[f89,f210])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl2_15 | ~spl2_9 | ~spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f174,f169,f120,f208])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl2_9 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl2_11 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_9 | ~spl2_11)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f122,f171,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl2_11 | ~spl2_7 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f128,f120,f102,f169])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl2_7 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl2_7 | ~spl2_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_9),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f122,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_7),
% 0.21/0.51    inference(resolution,[],[f104,f43])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f102])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl2_10 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f124,f120,f133])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl2_9 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f93,f67,f120])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f69,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl2_8 | ~spl2_1 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f98,f67,f62,f113])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f64,f69,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl2_7 | ~spl2_1 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f67,f62,f102])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f64,f69,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl2_5 | spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f87,f82])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~spl2_3 | ~spl2_5 | ~spl2_4 | ~spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f91,f87,f76,f82,f72])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f89])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | ~spl2_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f41,f78])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl2_3 | spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f76,f72])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f67])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (10521)------------------------------
% 0.21/0.51  % (10521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10521)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (10521)Memory used [KB]: 11001
% 0.21/0.51  % (10521)Time elapsed: 0.092 s
% 0.21/0.51  % (10521)------------------------------
% 0.21/0.51  % (10521)------------------------------
% 0.21/0.51  % (10505)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (10503)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (10497)Success in time 0.148 s
%------------------------------------------------------------------------------
