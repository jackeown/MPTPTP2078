%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t30_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:27 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 691 expanded)
%              Number of leaves         :   78 ( 292 expanded)
%              Depth                    :   10
%              Number of atoms          :  740 (1733 expanded)
%              Number of equality atoms :   47 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f732,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f94,f101,f108,f115,f129,f130,f149,f154,f161,f170,f180,f193,f210,f224,f243,f251,f265,f279,f300,f314,f328,f343,f350,f357,f368,f375,f382,f437,f451,f465,f472,f479,f494,f495,f508,f517,f528,f577,f588,f602,f617,f624,f664,f672,f680,f684,f705,f714,f717,f731])).

fof(f731,plain,
    ( ~ spl4_101
    | ~ spl4_0
    | spl4_11
    | ~ spl4_12
    | ~ spl4_32
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f688,f449,f241,f127,f118,f85,f729])).

fof(f729,plain,
    ( spl4_101
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f85,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f118,plain,
    ( spl4_11
  <=> ~ v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f127,plain,
    ( spl4_12
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f241,plain,
    ( spl4_32
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f449,plain,
    ( spl4_62
  <=> k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f688,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_32
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f687,f450])).

fof(f450,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f449])).

fof(f687,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f686,f119])).

fof(f119,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f686,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f685,f242])).

fof(f242,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f241])).

fof(f685,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f673,f86])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f85])).

fof(f673,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f128,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t29_tops_1)).

fof(f128,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f717,plain,
    ( ~ spl4_48
    | ~ spl4_74 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | ~ spl4_48
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f327,f521])).

fof(f521,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_74 ),
    inference(resolution,[],[f516,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t7_boole)).

fof(f516,plain,
    ( r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl4_74
  <=> r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f327,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl4_48
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f714,plain,
    ( spl4_98
    | spl4_49
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f707,f697,f323,f712])).

fof(f712,plain,
    ( spl4_98
  <=> r2_hidden(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f323,plain,
    ( spl4_49
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f697,plain,
    ( spl4_94
  <=> m1_subset_1(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f707,plain,
    ( r2_hidden(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_49
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f706,f324])).

fof(f324,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f323])).

fof(f706,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_94 ),
    inference(resolution,[],[f698,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t2_subset)).

fof(f698,plain,
    ( m1_subset_1(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f697])).

fof(f705,plain,
    ( spl4_94
    | spl4_96
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f649,f449,f703,f697])).

fof(f703,plain,
    ( spl4_96
  <=> v1_xboole_0(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f649,plain,
    ( v1_xboole_0(sK2(k1_xboole_0))
    | m1_subset_1(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f638,f450])).

fof(f638,plain,
    ( m1_subset_1(sK2(sK2(k1_xboole_0)),u1_struct_0(sK0))
    | v1_xboole_0(sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_62 ),
    inference(superposition,[],[f287,f450])).

fof(f287,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(sK2(k1_zfmisc_1(X2))),X2)
      | v1_xboole_0(sK2(k1_zfmisc_1(X2))) ) ),
    inference(resolution,[],[f230,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',existence_m1_subset_1)).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK2(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f77,f132])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f68])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t4_subset)).

fof(f684,plain,
    ( ~ spl4_8
    | spl4_65 ),
    inference(avatar_contradiction_clause,[],[f683])).

fof(f683,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f681,f114])).

fof(f114,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f681,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_65 ),
    inference(resolution,[],[f468,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',dt_k3_subset_1)).

fof(f468,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl4_65
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f680,plain,
    ( ~ spl4_93
    | ~ spl4_62
    | spl4_67 ),
    inference(avatar_split_clause,[],[f630,f477,f449,f678])).

fof(f678,plain,
    ( spl4_93
  <=> ~ r2_hidden(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f477,plain,
    ( spl4_67
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f630,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_62
    | ~ spl4_67 ),
    inference(superposition,[],[f478,f450])).

fof(f478,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f477])).

fof(f672,plain,
    ( ~ spl4_91
    | spl4_19
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f629,f449,f159,f670])).

fof(f670,plain,
    ( spl4_91
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f159,plain,
    ( spl4_19
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f629,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl4_19
    | ~ spl4_62 ),
    inference(superposition,[],[f160,f450])).

fof(f160,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f664,plain,
    ( spl4_88
    | ~ spl4_8
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f628,f449,f113,f662])).

fof(f662,plain,
    ( spl4_88
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f628,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_62 ),
    inference(superposition,[],[f114,f450])).

fof(f624,plain,
    ( ~ spl4_0
    | ~ spl4_10
    | spl4_13
    | ~ spl4_32
    | ~ spl4_64 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_32
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f622,f125])).

fof(f125,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_13
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f622,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_0
    | ~ spl4_10
    | ~ spl4_32
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f621,f471])).

fof(f471,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl4_64
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f621,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_0
    | ~ spl4_10
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f619,f122])).

fof(f122,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_10
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f619,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(superposition,[],[f580,f242])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f66,f86])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f617,plain,
    ( spl4_86
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f610,f600,f615])).

fof(f615,plain,
    ( spl4_86
  <=> m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f600,plain,
    ( spl4_84
  <=> k1_xboole_0 = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f610,plain,
    ( m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_84 ),
    inference(superposition,[],[f68,f601])).

fof(f601,plain,
    ( k1_xboole_0 = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f600])).

fof(f602,plain,
    ( spl4_84
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f593,f586,f178,f168,f600])).

fof(f168,plain,
    ( spl4_20
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f178,plain,
    ( spl4_22
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f586,plain,
    ( spl4_82
  <=> v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f593,plain,
    ( k1_xboole_0 = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f589,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f178])).

fof(f589,plain,
    ( sK2(k1_zfmisc_1(k1_xboole_0)) = sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_20
    | ~ spl4_82 ),
    inference(resolution,[],[f587,f172])).

fof(f172,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK2(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_20 ),
    inference(resolution,[],[f169,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t8_boole)).

fof(f169,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f587,plain,
    ( v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f586])).

fof(f588,plain,
    ( spl4_82
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f578,f569,f586])).

fof(f569,plain,
    ( spl4_78
  <=> ! [X1] : ~ r2_hidden(X1,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f578,plain,
    ( v1_xboole_0(sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_78 ),
    inference(resolution,[],[f570,f132])).

fof(f570,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f569])).

fof(f577,plain,
    ( spl4_78
    | spl4_80
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f385,f99,f575,f569])).

fof(f575,plain,
    ( spl4_80
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f99,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f385,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X1,sK2(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f287,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f78,f100])).

fof(f100,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t5_subset)).

fof(f528,plain,
    ( ~ spl4_77
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f520,f515,f526])).

fof(f526,plain,
    ( spl4_77
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f520,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_74 ),
    inference(resolution,[],[f516,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',antisymmetry_r2_hidden)).

fof(f517,plain,
    ( spl4_74
    | spl4_49
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f510,f506,f323,f515])).

fof(f506,plain,
    ( spl4_72
  <=> m1_subset_1(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f510,plain,
    ( r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_49
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f509,f324])).

fof(f509,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_72 ),
    inference(resolution,[],[f507,f71])).

fof(f507,plain,
    ( m1_subset_1(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f506])).

fof(f508,plain,
    ( spl4_70
    | spl4_72
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f482,f470,f506,f500])).

fof(f500,plain,
    ( spl4_70
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f482,plain,
    ( m1_subset_1(sK2(k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_64 ),
    inference(resolution,[],[f471,f230])).

fof(f495,plain,
    ( spl4_60
    | spl4_16
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f425,f113,f147,f435])).

fof(f435,plain,
    ( spl4_60
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f147,plain,
    ( spl4_16
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f425,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(resolution,[],[f229,f114])).

fof(f229,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3))
      | r2_hidden(k3_subset_1(X3,X2),k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f72,f71])).

fof(f494,plain,
    ( spl4_68
    | ~ spl4_32
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f487,f470,f241,f492])).

fof(f492,plain,
    ( spl4_68
  <=> k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f487,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_32
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f481,f242])).

fof(f481,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_64 ),
    inference(resolution,[],[f471,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',d5_subset_1)).

fof(f479,plain,
    ( ~ spl4_67
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f462,f435,f477])).

fof(f462,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_60 ),
    inference(resolution,[],[f436,f69])).

fof(f436,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f435])).

fof(f472,plain,
    ( spl4_64
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f461,f435,f470])).

fof(f461,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_60 ),
    inference(resolution,[],[f436,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t1_subset)).

fof(f465,plain,
    ( ~ spl4_0
    | spl4_11
    | ~ spl4_12
    | ~ spl4_32
    | ~ spl4_60 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_32
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f461,f459])).

fof(f459,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f458,f119])).

fof(f458,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f457,f242])).

fof(f457,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f456,f86])).

fof(f456,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f65,f128])).

fof(f451,plain,
    ( spl4_62
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f442,f178,f168,f147,f449])).

fof(f442,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f438,f179])).

fof(f438,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(resolution,[],[f148,f172])).

fof(f148,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f437,plain,
    ( spl4_60
    | ~ spl4_8
    | spl4_17 ),
    inference(avatar_split_clause,[],[f430,f144,f113,f435])).

fof(f144,plain,
    ( spl4_17
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f430,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f425,f145])).

fof(f145,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f382,plain,
    ( spl4_58
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f360,f113,f380])).

fof(f380,plain,
    ( spl4_58
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f360,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f74,f114])).

fof(f375,plain,
    ( ~ spl4_57
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f366,f320,f373])).

fof(f373,plain,
    ( spl4_57
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f320,plain,
    ( spl4_46
  <=> r2_hidden(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f366,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK1))
    | ~ spl4_46 ),
    inference(resolution,[],[f321,f69])).

fof(f321,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f320])).

fof(f368,plain,
    ( ~ spl4_49
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f367,f320,f323])).

fof(f367,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_46 ),
    inference(resolution,[],[f321,f76])).

fof(f357,plain,
    ( spl4_54
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f331,f312,f113,f355])).

fof(f355,plain,
    ( spl4_54
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f312,plain,
    ( spl4_44
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f331,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(superposition,[],[f114,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f312])).

fof(f350,plain,
    ( ~ spl4_53
    | spl4_43
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f329,f312,f295,f348])).

fof(f348,plain,
    ( spl4_53
  <=> ~ m1_subset_1(sK2(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f295,plain,
    ( spl4_43
  <=> ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f329,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl4_43
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f296,f313])).

fof(f296,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f295])).

fof(f343,plain,
    ( ~ spl4_51
    | spl4_11
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f332,f312,f118,f341])).

fof(f341,plain,
    ( spl4_51
  <=> ~ v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f332,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_11
    | ~ spl4_44 ),
    inference(superposition,[],[f119,f313])).

fof(f328,plain,
    ( spl4_46
    | spl4_48
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f315,f298,f326,f320])).

fof(f298,plain,
    ( spl4_42
  <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f315,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl4_42 ),
    inference(resolution,[],[f299,f71])).

fof(f299,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f298])).

fof(f314,plain,
    ( spl4_44
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f305,f292,f178,f168,f312])).

fof(f292,plain,
    ( spl4_40
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f305,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f301,f179])).

fof(f301,plain,
    ( sK1 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_40 ),
    inference(resolution,[],[f293,f172])).

fof(f293,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f292])).

fof(f300,plain,
    ( spl4_40
    | spl4_42
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f286,f113,f298,f292])).

fof(f286,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f230,f114])).

fof(f279,plain,
    ( spl4_38
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f270,f263,f178,f168,f277])).

fof(f277,plain,
    ( spl4_38
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f263,plain,
    ( spl4_36
  <=> v1_xboole_0(k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f270,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f266,f179])).

fof(f266,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_36 ),
    inference(resolution,[],[f264,f172])).

fof(f264,plain,
    ( v1_xboole_0(k3_subset_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl4_36
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f256,f191,f99,f263])).

fof(f191,plain,
    ( spl4_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f256,plain,
    ( v1_xboole_0(k3_subset_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(resolution,[],[f253,f192])).

fof(f192,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f191])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(k3_subset_1(k1_xboole_0,X0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f228,f132])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_subset_1(k1_xboole_0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f72,f150])).

fof(f251,plain,
    ( spl4_34
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f234,f191,f249])).

fof(f249,plain,
    ( spl4_34
  <=> k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f234,plain,
    ( k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | ~ spl4_24 ),
    inference(resolution,[],[f73,f192])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',involutiveness_k3_subset_1)).

fof(f243,plain,
    ( spl4_32
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f235,f113,f241])).

fof(f235,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_8 ),
    inference(resolution,[],[f73,f114])).

fof(f224,plain,
    ( spl4_30
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f215,f202,f178,f168,f222])).

fof(f222,plain,
    ( spl4_30
  <=> k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f202,plain,
    ( spl4_26
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f215,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f211,f179])).

fof(f211,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_26 ),
    inference(resolution,[],[f203,f172])).

fof(f203,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f202])).

fof(f210,plain,
    ( spl4_26
    | spl4_28
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f184,f178,f208,f202])).

fof(f208,plain,
    ( spl4_28
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f184,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f132,f179])).

fof(f193,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f185,f178,f191])).

fof(f185,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f68,f179])).

fof(f180,plain,
    ( spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f173,f168,f178])).

fof(f173,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(resolution,[],[f169,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t6_boole)).

fof(f170,plain,
    ( spl4_20
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f163,f99,f168])).

fof(f163,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f162,f132])).

fof(f162,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f150,f68])).

fof(f161,plain,
    ( ~ spl4_19
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f152,f141,f159])).

fof(f141,plain,
    ( spl4_14
  <=> r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f152,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl4_14 ),
    inference(resolution,[],[f142,f69])).

fof(f142,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f154,plain,
    ( ~ spl4_17
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f153,f141,f144])).

fof(f153,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(resolution,[],[f142,f76])).

fof(f149,plain,
    ( spl4_14
    | spl4_16
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f133,f113,f147,f141])).

fof(f133,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(resolution,[],[f71,f114])).

fof(f130,plain,
    ( ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f60,f124,f118])).

fof(f60,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v3_pre_topc(X1,sK0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | ~ v3_pre_topc(sK1,X0) )
        & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',t30_tops_1)).

fof(f129,plain,
    ( spl4_10
    | spl4_12 ),
    inference(avatar_split_clause,[],[f59,f127,f121])).

fof(f59,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f58,f113])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f108,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f62,f106])).

fof(f106,plain,
    ( spl4_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',d2_xboole_0)).

fof(f101,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f80,f99])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f61,f62])).

fof(f61,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',dt_o_0_0_xboole_0)).

fof(f94,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f79,f92])).

fof(f92,plain,
    ( spl4_2
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f55])).

fof(f55,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t30_tops_1.p',existence_l1_pre_topc)).

fof(f87,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f57,f85])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
