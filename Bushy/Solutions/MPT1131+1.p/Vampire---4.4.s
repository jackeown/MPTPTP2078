%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t62_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:46 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 791 expanded)
%              Number of leaves         :   46 ( 302 expanded)
%              Depth                    :   17
%              Number of atoms          : 1242 (3548 expanded)
%              Number of equality atoms :   11 ( 122 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f791,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f107,f114,f121,f128,f135,f142,f149,f156,f163,f170,f183,f184,f203,f268,f278,f300,f305,f330,f411,f467,f477,f484,f509,f536,f543,f547,f548,f553,f560,f696,f734,f790])).

fof(f790,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_38
    | ~ spl7_52
    | spl7_55
    | ~ spl7_62 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_38
    | ~ spl7_52
    | ~ spl7_55
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f788,f692])).

fof(f692,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f691])).

fof(f691,plain,
    ( spl7_62
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f788,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_38
    | ~ spl7_52
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f787,f535])).

fof(f535,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl7_52
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f787,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_38
    | ~ spl7_55 ),
    inference(resolution,[],[f738,f542])).

fof(f542,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl7_55
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f738,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_38 ),
    inference(resolution,[],[f736,f314])).

fof(f314,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(k10_relat_1(sK2,X1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v4_pre_topc(k10_relat_1(sK2,X1),sK0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f313,f120])).

fof(f120,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f313,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(k10_relat_1(sK2,X1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(sK0)
        | v4_pre_topc(k10_relat_1(sK2,X1),sK0) )
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f310,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f310,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(k10_relat_1(sK2,X1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(sK0)
        | v4_pre_topc(k10_relat_1(sK2,X1),sK0) )
    | ~ spl7_20 ),
    inference(resolution,[],[f287,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',t61_pre_topc)).

fof(f287,plain,
    ( ! [X1] : m1_subset_1(k10_relat_1(sK2,X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f281,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f281,plain,
    ( ! [X1] :
        ( m1_subset_1(k10_relat_1(sK2,X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) )
    | ~ spl7_20 ),
    inference(superposition,[],[f80,f217])).

fof(f217,plain,
    ( ! [X1] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl7_20 ),
    inference(resolution,[],[f86,f169])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',redefinition_k8_relset_1)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',dt_k8_relset_1)).

fof(f736,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f528,f179])).

fof(f179,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_24
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f528,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f527,f296])).

fof(f296,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl7_38
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f527,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f526,f169])).

fof(f526,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f525,f162])).

fof(f162,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_18
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f525,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f524,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f524,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) )
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f280,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f280,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) )
    | ~ spl7_20 ),
    inference(superposition,[],[f65,f217])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | ~ l1_pre_topc(X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',d12_pre_topc)).

fof(f734,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | spl7_23
    | spl7_63 ),
    inference(avatar_contradiction_clause,[],[f733])).

fof(f733,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_23
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f732,f176])).

fof(f176,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_23
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f732,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f731,f127])).

fof(f731,plain,
    ( ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f730,f148])).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f730,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f729,f141])).

fof(f141,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_12
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f729,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f728,f99])).

fof(f728,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f726,f113])).

fof(f726,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_63 ),
    inference(resolution,[],[f695,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f695,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl7_63
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f696,plain,
    ( ~ spl7_63
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | spl7_51
    | ~ spl7_52
    | spl7_55 ),
    inference(avatar_split_clause,[],[f651,f541,f534,f482,f295,f168,f161,f126,f119,f112,f98,f694])).

fof(f482,plain,
    ( spl7_51
  <=> ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f651,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | ~ spl7_51
    | ~ spl7_52
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f650,f535])).

fof(f650,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | ~ spl7_51
    | ~ spl7_55 ),
    inference(resolution,[],[f634,f542])).

fof(f634,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | ~ spl7_51 ),
    inference(resolution,[],[f314,f529])).

fof(f529,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f528,f507])).

fof(f507,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f506,f296])).

fof(f506,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f505,f169])).

fof(f505,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f504,f162])).

fof(f504,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f503,f99])).

fof(f503,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_4
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f501,f113])).

fof(f501,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_51 ),
    inference(resolution,[],[f483,f66])).

fof(f483,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f482])).

fof(f560,plain,
    ( ~ spl7_61
    | ~ spl7_4
    | spl7_51 ),
    inference(avatar_split_clause,[],[f510,f482,f112,f558])).

fof(f558,plain,
    ( spl7_61
  <=> ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f510,plain,
    ( ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),u1_pre_topc(sK1))
    | ~ spl7_4
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f502,f113])).

fof(f502,plain,
    ( ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_51 ),
    inference(resolution,[],[f483,f206])).

fof(f206,plain,(
    ! [X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r2_hidden(X2,u1_pre_topc(X3))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f82,f79])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',dt_u1_pre_topc)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',t4_subset)).

fof(f553,plain,
    ( ~ spl7_23
    | spl7_58
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f260,f147,f140,f126,f112,f98,f551,f175])).

fof(f551,plain,
    ( spl7_58
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f260,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f259,f127])).

fof(f259,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f258,f148])).

fof(f258,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f257,f141])).

fof(f257,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f256,f99])).

fof(f256,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f254,f113])).

fof(f254,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_14 ),
    inference(superposition,[],[f65,f216])).

fof(f216,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl7_14 ),
    inference(resolution,[],[f86,f148])).

fof(f548,plain,
    ( spl7_24
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38
    | spl7_51 ),
    inference(avatar_split_clause,[],[f507,f482,f295,f168,f161,f112,f98,f178])).

fof(f547,plain,
    ( spl7_56
    | spl7_22
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f514,f147,f140,f126,f112,f98,f172,f545])).

fof(f545,plain,
    ( spl7_56
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f172,plain,
    ( spl7_22
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f514,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f513,f127])).

fof(f513,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f512,f113])).

fof(f512,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f511,f141])).

fof(f511,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f380,f99])).

fof(f380,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f242,f148])).

fof(f242,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X8),u1_struct_0(X6))
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(X8)
      | v5_pre_topc(X7,X8,X6)
      | ~ r2_hidden(X9,sK4(X8,X6,X7))
      | m1_subset_1(X9,u1_struct_0(X6)) ) ),
    inference(resolution,[],[f66,f82])).

fof(f543,plain,
    ( spl7_22
    | ~ spl7_55
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f519,f147,f140,f126,f112,f98,f541,f172])).

fof(f519,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f518,f127])).

fof(f518,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f517,f148])).

fof(f517,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f516,f141])).

fof(f516,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f515,f99])).

fof(f515,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f251,f113])).

fof(f251,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_14 ),
    inference(superposition,[],[f68,f216])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f536,plain,
    ( spl7_22
    | spl7_52
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f523,f147,f140,f126,f112,f98,f534,f172])).

fof(f523,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f522,f127])).

fof(f522,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f521,f141])).

fof(f521,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f520,f99])).

fof(f520,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f232,f113])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f67,f148])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f509,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25
    | ~ spl7_38
    | spl7_51 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_38
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f507,f182])).

fof(f182,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_25
  <=> ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f484,plain,
    ( ~ spl7_51
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_36
    | spl7_47 ),
    inference(avatar_split_clause,[],[f469,f465,f292,f172,f147,f140,f126,f112,f98,f482])).

fof(f292,plain,
    ( spl7_36
  <=> v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f465,plain,
    ( spl7_47
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f469,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_36
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f468,f293])).

fof(f293,plain,
    ( v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f292])).

fof(f468,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_47 ),
    inference(resolution,[],[f466,f261])).

fof(f261,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f260,f173])).

fof(f173,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f466,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f465])).

fof(f477,plain,
    ( ~ spl7_39
    | ~ spl7_49
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25 ),
    inference(avatar_split_clause,[],[f286,f181,f168,f161,f112,f98,f475,f298])).

fof(f298,plain,
    ( spl7_39
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f475,plain,
    ( spl7_49
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f286,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f285,f182])).

fof(f285,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f284,f169])).

fof(f284,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f283,f162])).

fof(f283,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f282,f99])).

fof(f282,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f279,f113])).

fof(f279,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_20 ),
    inference(superposition,[],[f68,f217])).

fof(f467,plain,
    ( ~ spl7_47
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25 ),
    inference(avatar_split_clause,[],[f458,f181,f168,f161,f147,f126,f119,f112,f98,f465])).

fof(f458,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f457,f217])).

fof(f457,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f456,f113])).

fof(f456,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f455,f120])).

fof(f455,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f454,f127])).

fof(f454,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f453,f182])).

fof(f453,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f452,f169])).

fof(f452,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f451,f162])).

fof(f451,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f450,f99])).

fof(f450,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f445,f227])).

fof(f227,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f226,f148])).

fof(f226,plain,
    ( ! [X0] :
        ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f80,f216])).

fof(f445,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_20 ),
    inference(superposition,[],[f252,f217])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0))))
      | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f250,f188])).

fof(f188,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',dt_g1_pre_topc)).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),X2)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f68,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f411,plain,
    ( ~ spl7_43
    | spl7_44
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f379,f295,f181,f168,f161,f112,f98,f409,f406])).

fof(f406,plain,
    ( spl7_43
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f409,plain,
    ( spl7_44
  <=> ! [X1] : ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f379,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f378,f182])).

fof(f378,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f377,f296])).

fof(f377,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f376,f113])).

fof(f376,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f375,f162])).

fof(f375,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f372,f99])).

fof(f372,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ r2_hidden(X1,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_20 ),
    inference(resolution,[],[f243,f169])).

fof(f243,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X10))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X12),u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(X12)
      | v5_pre_topc(X11,X12,X10)
      | ~ r2_hidden(X13,sK4(X12,X10,X11))
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(resolution,[],[f66,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',t5_subset)).

fof(f330,plain,
    ( ~ spl7_41
    | spl7_34
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f312,f168,f276,f328])).

fof(f328,plain,
    ( spl7_41
  <=> ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f276,plain,
    ( spl7_34
  <=> ! [X3,X2] : ~ r2_hidden(X2,k10_relat_1(sK2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f312,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k10_relat_1(sK2,X5))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl7_20 ),
    inference(resolution,[],[f287,f81])).

fof(f305,plain,
    ( ~ spl7_8
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f303,f127])).

fof(f303,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_39 ),
    inference(resolution,[],[f188,f299])).

fof(f299,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f298])).

fof(f300,plain,
    ( spl7_36
    | ~ spl7_39
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25 ),
    inference(avatar_split_clause,[],[f239,f181,f168,f161,f112,f98,f298,f292])).

fof(f239,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f238,f182])).

fof(f238,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f237,f162])).

fof(f237,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f236,f99])).

fof(f236,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f233,f113])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_20 ),
    inference(resolution,[],[f67,f169])).

fof(f278,plain,
    ( ~ spl7_33
    | spl7_34
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f249,f147,f276,f273])).

fof(f273,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f249,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK2,X3))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f227,f81])).

fof(f268,plain,
    ( ~ spl7_31
    | spl7_28
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f191,f168,f201,f266])).

fof(f266,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f201,plain,
    ( spl7_28
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) )
    | ~ spl7_20 ),
    inference(resolution,[],[f81,f169])).

fof(f203,plain,
    ( ~ spl7_27
    | spl7_28
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f190,f147,f201,f198])).

fof(f198,plain,
    ( spl7_27
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f81,f148])).

fof(f184,plain,
    ( spl7_22
    | spl7_24 ),
    inference(avatar_split_clause,[],[f93,f178,f172])).

fof(f93,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f52,f57])).

fof(f57,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',t62_pre_topc)).

fof(f52,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f183,plain,
    ( ~ spl7_23
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f92,f181,f175])).

fof(f92,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f53,f57])).

fof(f53,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f170,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f89,f168])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f56,f57])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f163,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f90,f161])).

fof(f90,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f55,f57])).

fof(f55,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f156,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f87,f154])).

fof(f154,plain,
    ( spl7_16
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f87,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t62_pre_topc.p',existence_l1_pre_topc)).

fof(f149,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f60,f147])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f142,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f59,f140])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f135,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f133,plain,
    ( spl7_10
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f128,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f64,f126])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f121,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f114,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f62,f112])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f61,f105])).

fof(f105,plain,
    ( spl7_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f58,f98])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
