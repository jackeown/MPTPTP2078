%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t13_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 378 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f96,f97,f116,f128,f142,f146])).

fof(f146,plain,
    ( ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f143,f89])).

fof(f89,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_6
  <=> v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f143,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f68,f82,f92,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
           => v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t13_tops_2.p',l13_tops_2)).

fof(f92,plain,
    ( ~ v1_finset_1(sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_9
  <=> ~ v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f68,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f142,plain,
    ( ~ spl4_0
    | spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f140,f95])).

fof(f95,plain,
    ( v1_finset_1(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_8
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f140,plain,
    ( ~ v1_finset_1(sK1)
    | ~ spl4_0
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f138,f115])).

fof(f115,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_10
  <=> k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f138,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f68,f86,f127,f51])).

fof(f127,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_12
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f86,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_7
  <=> ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f128,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f81,f126])).

fof(f118,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t13_tops_2.p',dt_k7_setfam_1)).

fof(f116,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f109,f81,f114])).

fof(f109,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t13_tops_2.p',involutiveness_k7_setfam_1)).

fof(f97,plain,
    ( ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f49,f91,f85])).

fof(f49,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ v1_finset_1(sK1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & ( v1_finset_1(sK1)
      | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ v1_finset_1(sK1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1)) )
        & ( v1_finset_1(sK1)
          | v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1)) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <~> v1_finset_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
            <=> v1_finset_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t13_tops_2.p',t13_tops_2)).

fof(f96,plain,
    ( spl4_6
    | spl4_8 ),
    inference(avatar_split_clause,[],[f48,f94,f88])).

fof(f48,plain,
    ( v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f47,f81])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f62,f74])).

fof(f74,plain,
    ( spl4_2
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f44])).

fof(f44,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t13_tops_2.p',existence_l1_struct_0)).

fof(f69,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f46,f67])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
