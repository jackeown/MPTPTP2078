%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 213 expanded)
%              Number of leaves         :   25 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :  245 ( 565 expanded)
%              Number of equality atoms :   60 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2010,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f91,f96,f101,f317,f404,f416,f528,f530,f543,f615,f1751,f1760,f1762,f2002])).

fof(f2002,plain,
    ( spl2_2
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f1993,f1731,f87])).

fof(f87,plain,
    ( spl2_2
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1731,plain,
    ( spl2_109
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f1993,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_109 ),
    inference(superposition,[],[f110,f1733])).

fof(f1733,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_109 ),
    inference(avatar_component_clause,[],[f1731])).

fof(f110,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1762,plain,
    ( spl2_109
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f1761,f252,f1731])).

fof(f252,plain,
    ( spl2_20
  <=> k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1761,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f1758,f75])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1758,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_xboole_0)))
    | ~ spl2_20 ),
    inference(superposition,[],[f78,f254])).

fof(f254,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f252])).

fof(f78,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f59,f58,f74,f74])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1760,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f1757,f252,f93,f524])).

fof(f524,plain,
    ( spl2_35
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f93,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1757,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(superposition,[],[f337,f254])).

fof(f337,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f95,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1751,plain,
    ( ~ spl2_35
    | ~ spl2_3
    | spl2_20 ),
    inference(avatar_split_clause,[],[f1740,f252,f93,f524])).

fof(f1740,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | spl2_20 ),
    inference(superposition,[],[f253,f337])).

fof(f253,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f252])).

fof(f615,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f614,f305,f98,f93,f524])).

fof(f98,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f305,plain,
    ( spl2_24
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f614,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f603,f307])).

fof(f307,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f305])).

fof(f603,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f394,f95])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f50,f100])).

fof(f100,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f543,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f540,f98,f83,f93,f305])).

fof(f83,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f540,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f84,f303])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ v2_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f51,f100])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f84,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f530,plain,
    ( ~ spl2_24
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f329,f98,f93,f83,f305])).

fof(f329,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f100,f85,f95,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f528,plain,
    ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f416,plain,
    ( spl2_20
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f413,f148,f252])).

fof(f148,plain,
    ( spl2_9
  <=> k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f413,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_9 ),
    inference(superposition,[],[f77,f150])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f404,plain,
    ( spl2_31
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f392,f98,f93,f401])).

fof(f401,plain,
    ( spl2_31
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f392,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f100,f95,f50])).

fof(f317,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f314,f87,f148])).

fof(f314,plain,
    ( k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f88,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f101,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f44,f98])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f96,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f93])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f46,f87,f83])).

fof(f46,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f47,f87,f83])).

fof(f47,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (28809)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (28811)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (28802)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (28804)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (28806)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (28812)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (28803)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (28799)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (28810)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (28813)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (28801)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (28814)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (28800)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (28805)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (28816)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (28815)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (28808)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (28807)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.56  % (28805)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f2010,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f90,f91,f96,f101,f317,f404,f416,f528,f530,f543,f615,f1751,f1760,f1762,f2002])).
% 0.21/0.56  fof(f2002,plain,(
% 0.21/0.56    spl2_2 | ~spl2_109),
% 0.21/0.56    inference(avatar_split_clause,[],[f1993,f1731,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    spl2_2 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.56  fof(f1731,plain,(
% 0.21/0.56    spl2_109 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 0.21/0.56  fof(f1993,plain,(
% 0.21/0.56    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl2_109),
% 0.21/0.56    inference(superposition,[],[f110,f1733])).
% 0.21/0.56  fof(f1733,plain,(
% 0.21/0.56    sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_109),
% 0.21/0.56    inference(avatar_component_clause,[],[f1731])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.21/0.56    inference(superposition,[],[f76,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f55,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.56  fof(f1762,plain,(
% 0.21/0.56    spl2_109 | ~spl2_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f1761,f252,f1731])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    spl2_20 <=> k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.56  fof(f1761,plain,(
% 0.21/0.56    sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_20),
% 0.21/0.56    inference(forward_demodulation,[],[f1758,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f48,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f60,f58])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f1758,plain,(
% 0.21/0.56    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_xboole_0))) | ~spl2_20),
% 0.21/0.56    inference(superposition,[],[f78,f254])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f252])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f59,f58,f74,f74])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.56  fof(f1760,plain,(
% 0.21/0.56    spl2_35 | ~spl2_3 | ~spl2_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f1757,f252,f93,f524])).
% 0.21/0.56  fof(f524,plain,(
% 0.21/0.56    spl2_35 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.56  fof(f1757,plain,(
% 0.21/0.56    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_20)),
% 0.21/0.56    inference(superposition,[],[f337,f254])).
% 0.21/0.56  fof(f337,plain,(
% 0.21/0.56    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f95,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f67,f74])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f93])).
% 0.21/0.56  fof(f1751,plain,(
% 0.21/0.56    ~spl2_35 | ~spl2_3 | spl2_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f1740,f252,f93,f524])).
% 0.21/0.56  fof(f1740,plain,(
% 0.21/0.56    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | spl2_20)),
% 0.21/0.56    inference(superposition,[],[f253,f337])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    k1_xboole_0 != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | spl2_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f252])).
% 0.21/0.56  fof(f615,plain,(
% 0.21/0.56    spl2_35 | ~spl2_3 | ~spl2_4 | ~spl2_24),
% 0.21/0.56    inference(avatar_split_clause,[],[f614,f305,f98,f93,f524])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.56  fof(f305,plain,(
% 0.21/0.56    spl2_24 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.56  fof(f614,plain,(
% 0.21/0.56    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_24)),
% 0.21/0.56    inference(forward_demodulation,[],[f603,f307])).
% 0.21/0.56  fof(f307,plain,(
% 0.21/0.56    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_24),
% 0.21/0.56    inference(avatar_component_clause,[],[f305])).
% 0.21/0.56  fof(f603,plain,(
% 0.21/0.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.21/0.56    inference(resolution,[],[f394,f95])).
% 0.21/0.56  fof(f394,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_4),
% 0.21/0.56    inference(resolution,[],[f50,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f98])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.56  fof(f543,plain,(
% 0.21/0.56    spl2_24 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f540,f98,f83,f93,f305])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.56  fof(f540,plain,(
% 0.21/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_4)),
% 0.21/0.56    inference(resolution,[],[f84,f303])).
% 0.21/0.56  fof(f303,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0)) ) | ~spl2_4),
% 0.21/0.56    inference(resolution,[],[f51,f100])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f83])).
% 0.21/0.56  fof(f530,plain,(
% 0.21/0.56    ~spl2_24 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f329,f98,f93,f83,f305])).
% 0.21/0.56  fof(f329,plain,(
% 0.21/0.56    k1_xboole_0 != k1_tops_1(sK0,sK1) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f100,f85,f95,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f83])).
% 0.21/0.56  fof(f528,plain,(
% 0.21/0.56    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f416,plain,(
% 0.21/0.56    spl2_20 | ~spl2_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f413,f148,f252])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    spl2_9 <=> k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.56  fof(f413,plain,(
% 0.21/0.56    k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_9),
% 0.21/0.56    inference(superposition,[],[f77,f150])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f148])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f56,f74])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.56  fof(f404,plain,(
% 0.21/0.56    spl2_31 | ~spl2_3 | ~spl2_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f392,f98,f93,f401])).
% 0.21/0.56  fof(f401,plain,(
% 0.21/0.56    spl2_31 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.56  fof(f392,plain,(
% 0.21/0.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f100,f95,f50])).
% 0.21/0.56  fof(f317,plain,(
% 0.21/0.56    spl2_9 | ~spl2_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f314,f87,f148])).
% 0.21/0.56  fof(f314,plain,(
% 0.21/0.56    k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.56    inference(resolution,[],[f88,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f87])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl2_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f44,f98])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f22])).
% 0.21/0.56  fof(f22,conjecture,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    spl2_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f45,f93])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    spl2_1 | spl2_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f46,f87,f83])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ~spl2_1 | ~spl2_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f47,f87,f83])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (28805)------------------------------
% 0.21/0.56  % (28805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28805)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (28805)Memory used [KB]: 7291
% 0.21/0.56  % (28805)Time elapsed: 0.103 s
% 0.21/0.56  % (28805)------------------------------
% 0.21/0.56  % (28805)------------------------------
% 0.21/0.56  % (28798)Success in time 0.204 s
%------------------------------------------------------------------------------
