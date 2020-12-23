%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0817+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 144 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  252 ( 386 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f59,f63,f68,f73,f78,f90,f94,f99,f103,f154,f169,f172,f182,f198,f240,f247])).

fof(f247,plain,
    ( ~ spl4_2
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_35 ),
    inference(resolution,[],[f239,f45])).

fof(f45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f239,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_35
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f240,plain,
    ( spl4_35
    | ~ spl4_12
    | spl4_29 ),
    inference(avatar_split_clause,[],[f200,f195,f88,f238])).

fof(f88,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f195,plain,
    ( spl4_29
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f200,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl4_12
    | spl4_29 ),
    inference(resolution,[],[f197,f89])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f197,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( ~ spl4_22
    | ~ spl4_29
    | ~ spl4_9
    | spl4_27 ),
    inference(avatar_split_clause,[],[f183,f179,f76,f195,f147])).

fof(f147,plain,
    ( spl4_22
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f76,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f179,plain,
    ( spl4_27
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f183,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_27 ),
    inference(resolution,[],[f181,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f181,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f179])).

fof(f182,plain,
    ( ~ spl4_1
    | ~ spl4_27
    | ~ spl4_14
    | spl4_23 ),
    inference(avatar_split_clause,[],[f157,f151,f97,f179,f38])).

fof(f38,plain,
    ( spl4_1
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f97,plain,
    ( spl4_14
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f151,plain,
    ( spl4_23
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f157,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl4_14
    | spl4_23 ),
    inference(resolution,[],[f153,f98])).

fof(f98,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f153,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),k2_zfmisc_1(sK1,sK2))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f172,plain,
    ( ~ spl4_2
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(resolution,[],[f168,f45])).

fof(f168,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_25
  <=> ! [X1,X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f169,plain,
    ( spl4_25
    | ~ spl4_6
    | spl4_22 ),
    inference(avatar_split_clause,[],[f155,f147,f61,f167])).

fof(f61,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f155,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_6
    | spl4_22 ),
    inference(resolution,[],[f149,f62])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f149,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f147])).

fof(f154,plain,
    ( ~ spl4_22
    | ~ spl4_23
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f106,f101,f66,f151,f147])).

fof(f66,plain,
    ( spl4_7
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f101,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
        | ~ r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f106,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(resolution,[],[f102,f67])).

fof(f67,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl4_15
    | spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f95,f92,f70,f101])).

fof(f70,plain,
    ( spl4_8
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f92,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
        | ~ r1_tarski(sK3,X0) )
    | spl4_8
    | ~ spl4_13 ),
    inference(resolution,[],[f93,f72])).

fof(f72,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f99,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f36,f97])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f94,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f35,f92])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f90,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f73,plain,
    ( ~ spl4_8
    | spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f64,f57,f48,f70])).

fof(f48,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f57,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f64,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f68,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f63,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f59,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(k1_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(k1_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
