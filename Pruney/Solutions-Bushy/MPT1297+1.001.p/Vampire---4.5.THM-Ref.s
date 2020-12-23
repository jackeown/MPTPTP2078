%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1297+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 114 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  204 ( 434 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f32,f37,f42,f46,f50,f54,f60,f66,f78,f83])).

fof(f83,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f41,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f81,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f80,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f80,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f79,f30])).

fof(f30,plain,
    ( ~ v1_finset_1(sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( v1_finset_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(resolution,[],[f25,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
        | v1_finset_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_finset_1(X1)
        | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f25,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f78,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f77,f63,f57,f44,f39,f28,f24])).

fof(f57,plain,
    ( spl2_8
  <=> sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f63,plain,
    ( spl2_9
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f77,plain,
    ( ~ v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f76,f41])).

fof(f76,plain,
    ( ~ v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f70,f65])).

fof(f65,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f70,plain,
    ( ~ v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(superposition,[],[f45,f59])).

fof(f59,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f66,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f61,f52,f34,f63])).

fof(f52,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f61,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f53,f36])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f60,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f55,f48,f34,f57])).

fof(f48,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f55,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f54,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f50,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f46,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
           => v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_tops_2)).

fof(f42,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ v1_finset_1(sK1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & ( v1_finset_1(sK1)
      | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & ( v1_finset_1(X1)
              | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ( ~ v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
        & ( v1_finset_1(X1)
          | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ v1_finset_1(sK1)
        | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
      & ( v1_finset_1(sK1)
        | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <~> v1_finset_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
            <=> v1_finset_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tops_2)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f18,f28,f24])).

fof(f18,plain,
    ( v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f19,f28,f24])).

fof(f19,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
