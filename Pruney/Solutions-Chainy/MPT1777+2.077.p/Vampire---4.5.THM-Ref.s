%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  274 ( 560 expanded)
%              Number of leaves         :   54 ( 223 expanded)
%              Depth                    :   34
%              Number of atoms          : 1437 (3260 expanded)
%              Number of equality atoms :   38 ( 243 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f959,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f175,f180,f190,f202,f213,f218,f224,f232,f237,f253,f260,f265,f281,f291,f300,f311,f360,f366,f428,f466,f479,f485,f516,f557,f597,f731,f946,f953,f958])).

fof(f958,plain,
    ( ~ spl7_27
    | ~ spl7_45
    | spl7_81 ),
    inference(avatar_contradiction_clause,[],[f957])).

fof(f957,plain,
    ( $false
    | ~ spl7_27
    | ~ spl7_45
    | spl7_81 ),
    inference(subsumption_resolution,[],[f956,f472])).

fof(f472,plain,
    ( v2_pre_topc(sK2)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl7_45
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f956,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl7_27
    | spl7_81 ),
    inference(subsumption_resolution,[],[f954,f264])).

fof(f264,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl7_27
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f954,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl7_81 ),
    inference(resolution,[],[f952,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f952,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | spl7_81 ),
    inference(avatar_component_clause,[],[f950])).

fof(f950,plain,
    ( spl7_81
  <=> v3_pre_topc(k2_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f953,plain,
    ( ~ spl7_81
    | ~ spl7_27
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_54
    | ~ spl7_66
    | spl7_80 ),
    inference(avatar_split_clause,[],[f948,f943,f728,f554,f363,f357,f262,f950])).

fof(f357,plain,
    ( spl7_33
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f363,plain,
    ( spl7_34
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f554,plain,
    ( spl7_54
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f728,plain,
    ( spl7_66
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f943,plain,
    ( spl7_80
  <=> v3_pre_topc(k2_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f948,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ spl7_27
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_54
    | ~ spl7_66
    | spl7_80 ),
    inference(subsumption_resolution,[],[f947,f730])).

fof(f730,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f728])).

fof(f947,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_27
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_54
    | spl7_80 ),
    inference(resolution,[],[f945,f752])).

fof(f752,plain,
    ( ! [X1] :
        ( v3_pre_topc(X1,sK3)
        | ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) )
    | ~ spl7_27
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_54 ),
    inference(forward_demodulation,[],[f751,f359])).

fof(f359,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f357])).

fof(f751,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | v3_pre_topc(X1,sK3) )
    | ~ spl7_27
    | ~ spl7_34
    | ~ spl7_54 ),
    inference(resolution,[],[f744,f556])).

fof(f556,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f554])).

fof(f744,plain,
    ( ! [X8,X9] :
        ( ~ m1_pre_topc(X9,sK2)
        | ~ v3_pre_topc(X8,sK2)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
        | v3_pre_topc(X8,X9) )
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f743,f640])).

fof(f640,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) )
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f271,f365])).

fof(f365,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f363])).

fof(f271,plain,
    ( ! [X4,X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_27 ),
    inference(resolution,[],[f264,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f743,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_pre_topc(X9,sK2)
        | ~ v3_pre_topc(X8,sK2)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
        | v3_pre_topc(X8,X9) )
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f274,f365])).

fof(f274,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(X9,sK2)
        | ~ v3_pre_topc(X8,sK2)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
        | v3_pre_topc(X8,X9) )
    | ~ spl7_27 ),
    inference(resolution,[],[f264,f72])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f945,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | spl7_80 ),
    inference(avatar_component_clause,[],[f943])).

fof(f946,plain,
    ( ~ spl7_80
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f919,f594,f513,f482,f456,f425,f363,f357,f308,f257,f234,f215,f199,f128,f118,f113,f108,f103,f98,f93,f88,f83,f78,f943])).

fof(f78,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f83,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f88,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f93,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f98,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f103,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f108,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f113,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f118,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f128,plain,
    ( spl7_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f199,plain,
    ( spl7_18
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f215,plain,
    ( spl7_21
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f234,plain,
    ( spl7_24
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f257,plain,
    ( spl7_26
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f308,plain,
    ( spl7_31
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f425,plain,
    ( spl7_38
  <=> m1_subset_1(sK5,k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f456,plain,
    ( spl7_43
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f482,plain,
    ( spl7_46
  <=> v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f513,plain,
    ( spl7_50
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f594,plain,
    ( spl7_55
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f919,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f918,f515])).

fof(f515,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f513])).

fof(f918,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_46
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f917,f310])).

fof(f310,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f917,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_46
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f916,f365])).

fof(f916,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_46
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f915,f484])).

fof(f484,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f482])).

fof(f915,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f914,f310])).

fof(f914,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_18
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f913,f201])).

fof(f201,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f913,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f912,f217])).

fof(f217,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f912,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f911,f115])).

fof(f115,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f911,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f910,f110])).

fof(f110,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f910,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f909,f130])).

fof(f130,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f909,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f908,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f908,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f907,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f907,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f906,f100])).

fof(f100,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f906,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_9
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f905,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f905,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_9
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f904,f120])).

fof(f120,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f904,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f903,f596])).

fof(f596,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f594])).

fof(f903,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43 ),
    inference(resolution,[],[f815,f259])).

fof(f259,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f257])).

fof(f815,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),sK5)
        | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,sK3)
        | ~ v3_pre_topc(u1_struct_0(X1),sK3)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0))))
        | r1_tmap_1(sK3,X0,sK4,sK5) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_38
    | ~ spl7_43 ),
    inference(resolution,[],[f812,f427])).

fof(f427,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f425])).

fof(f812,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f708,f393])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) )
    | ~ spl7_24
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f384,f236])).

fof(f236,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f234])).

fof(f384,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl7_33 ),
    inference(superposition,[],[f62,f359])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f708,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f707,f359])).

fof(f707,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f706,f359])).

fof(f706,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f705,f359])).

fof(f705,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f704,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f704,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(duplicate_literal_removal,[],[f703])).

fof(f703,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3)
        | r1_tmap_1(sK3,X2,sK4,X3) )
    | ~ spl7_1
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(resolution,[],[f692,f139])).

fof(f139,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_tsep_1(X2,X3)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f137,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f137,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl7_1 ),
    inference(resolution,[],[f80,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f80,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f692,plain,
    ( ! [X10] :
        ( v1_tsep_1(X10,sK3)
        | ~ m1_pre_topc(X10,sK3)
        | ~ v3_pre_topc(u1_struct_0(X10),sK3)
        | ~ m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(k2_struct_0(sK3))) )
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f691,f359])).

fof(f691,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(X10,sK3)
        | ~ m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(X10),sK3)
        | v1_tsep_1(X10,sK3) )
    | ~ spl7_24
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f247,f457])).

fof(f457,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f456])).

fof(f247,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK3)
        | ~ m1_pre_topc(X10,sK3)
        | ~ m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(X10),sK3)
        | v1_tsep_1(X10,sK3) )
    | ~ spl7_24 ),
    inference(resolution,[],[f236,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f731,plain,
    ( spl7_66
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f712,f594,f363,f357,f234,f728])).

fof(f712,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f710,f365])).

fof(f710,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_55 ),
    inference(resolution,[],[f393,f596])).

fof(f597,plain,
    ( spl7_55
    | ~ spl7_22
    | ~ spl7_27
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f592,f297,f262,f221,f594])).

fof(f221,plain,
    ( spl7_22
  <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f297,plain,
    ( spl7_30
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f592,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_22
    | ~ spl7_27
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f591,f223])).

fof(f223,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f221])).

fof(f591,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_27
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f584,f264])).

fof(f584,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_27
    | ~ spl7_30 ),
    inference(resolution,[],[f269,f299])).

fof(f299,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f297])).

fof(f269,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_27 ),
    inference(resolution,[],[f264,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f557,plain,
    ( spl7_54
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f552,f288,f262,f234,f221,f554])).

fof(f288,plain,
    ( spl7_29
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f552,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f551,f290])).

fof(f290,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f288])).

fof(f551,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_pre_topc(sK3,sK2)
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f548,f223])).

fof(f548,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(sK3,sK2)
    | ~ spl7_24
    | ~ spl7_27 ),
    inference(resolution,[],[f240,f264])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | m1_pre_topc(sK3,X0) )
    | ~ spl7_24 ),
    inference(resolution,[],[f236,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f516,plain,
    ( spl7_50
    | ~ spl7_23
    | ~ spl7_31
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f486,f357,f308,f229,f513])).

fof(f229,plain,
    ( spl7_23
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f486,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_23
    | ~ spl7_31
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f318,f359])).

fof(f318,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_23
    | ~ spl7_31 ),
    inference(superposition,[],[f231,f310])).

fof(f231,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f229])).

fof(f485,plain,
    ( spl7_46
    | ~ spl7_20
    | ~ spl7_31
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f480,f357,f308,f210,f482])).

fof(f210,plain,
    ( spl7_20
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f480,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_20
    | ~ spl7_31
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f319,f359])).

fof(f319,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_20
    | ~ spl7_31 ),
    inference(superposition,[],[f212,f310])).

fof(f212,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f479,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | spl7_45 ),
    inference(subsumption_resolution,[],[f476,f135])).

fof(f135,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f476,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl7_8
    | ~ spl7_9
    | spl7_45 ),
    inference(resolution,[],[f473,f167])).

fof(f167,plain,
    ( ! [X5] :
        ( v2_pre_topc(X5)
        | ~ m1_pre_topc(X5,sK0) )
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f162,f115])).

fof(f162,plain,
    ( ! [X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X5,sK0)
        | v2_pre_topc(X5) )
    | ~ spl7_9 ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f473,plain,
    ( ~ v2_pre_topc(sK2)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f471])).

fof(f466,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_43 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | spl7_43 ),
    inference(subsumption_resolution,[],[f463,f130])).

fof(f463,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ spl7_8
    | ~ spl7_9
    | spl7_43 ),
    inference(resolution,[],[f458,f167])).

fof(f458,plain,
    ( ~ v2_pre_topc(sK3)
    | spl7_43 ),
    inference(avatar_component_clause,[],[f456])).

fof(f428,plain,
    ( spl7_38
    | ~ spl7_16
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f383,f357,f187,f425])).

fof(f187,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f383,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3))
    | ~ spl7_16
    | ~ spl7_33 ),
    inference(superposition,[],[f189,f359])).

fof(f189,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f366,plain,
    ( spl7_34
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f283,f278,f363])).

fof(f278,plain,
    ( spl7_28
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f283,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_28 ),
    inference(resolution,[],[f280,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f280,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f278])).

fof(f360,plain,
    ( spl7_33
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f255,f250,f357])).

fof(f250,plain,
    ( spl7_25
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f255,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_25 ),
    inference(resolution,[],[f252,f56])).

fof(f252,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f311,plain,
    ( spl7_31
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f191,f172,f308])).

fof(f172,plain,
    ( spl7_13
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f191,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_13 ),
    inference(resolution,[],[f174,f56])).

fof(f174,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f300,plain,
    ( spl7_30
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f267,f262,f297])).

fof(f267,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl7_27 ),
    inference(resolution,[],[f264,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f291,plain,
    ( spl7_29
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f239,f234,f288])).

fof(f239,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl7_24 ),
    inference(resolution,[],[f236,f58])).

fof(f281,plain,
    ( spl7_28
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f266,f262,f278])).

fof(f266,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_27 ),
    inference(resolution,[],[f264,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f265,plain,
    ( spl7_27
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f226,f133,f118,f262])).

fof(f226,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(resolution,[],[f160,f135])).

fof(f160,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | l1_pre_topc(X2) )
    | ~ spl7_9 ),
    inference(resolution,[],[f120,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f260,plain,
    ( spl7_26
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f254,f123,f257])).

fof(f123,plain,
    ( spl7_10
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f254,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f39,f125])).

fof(f125,plain,
    ( sK5 = sK6
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f39,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f253,plain,
    ( spl7_25
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f238,f234,f250])).

fof(f238,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_24 ),
    inference(resolution,[],[f236,f57])).

fof(f237,plain,
    ( spl7_24
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f225,f128,f118,f234])).

fof(f225,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(resolution,[],[f160,f130])).

fof(f232,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f44,f229])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f224,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f45,f221])).

fof(f45,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f218,plain,
    ( spl7_21
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f208,f177,f123,f215])).

fof(f177,plain,
    ( spl7_14
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f208,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f179,f125])).

fof(f179,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f213,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f43,f210])).

fof(f43,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f202,plain,(
    ~ spl7_18 ),
    inference(avatar_split_clause,[],[f40,f199])).

fof(f40,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f190,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f41,f187])).

fof(f41,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f37,f177])).

fof(f37,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f175,plain,
    ( spl7_13
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f141,f103,f172])).

fof(f141,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f105,f57])).

fof(f136,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f49,f133])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f47,f128])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f126,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f38,f123])).

fof(f38,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f55,f118])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f54,f113])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f111,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (22550)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (22551)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (22552)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (22560)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (22548)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (22558)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (22554)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (22568)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (22555)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (22556)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (22553)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (22557)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (22559)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (22561)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (22567)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (22547)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (22563)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (22551)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (22565)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (22562)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f959,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f175,f180,f190,f202,f213,f218,f224,f232,f237,f253,f260,f265,f281,f291,f300,f311,f360,f366,f428,f466,f479,f485,f516,f557,f597,f731,f946,f953,f958])).
% 0.22/0.54  fof(f958,plain,(
% 0.22/0.54    ~spl7_27 | ~spl7_45 | spl7_81),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f957])).
% 0.22/0.54  fof(f957,plain,(
% 0.22/0.54    $false | (~spl7_27 | ~spl7_45 | spl7_81)),
% 0.22/0.54    inference(subsumption_resolution,[],[f956,f472])).
% 0.22/0.54  fof(f472,plain,(
% 0.22/0.54    v2_pre_topc(sK2) | ~spl7_45),
% 0.22/0.54    inference(avatar_component_clause,[],[f471])).
% 0.22/0.54  fof(f471,plain,(
% 0.22/0.54    spl7_45 <=> v2_pre_topc(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.22/0.54  fof(f956,plain,(
% 0.22/0.54    ~v2_pre_topc(sK2) | (~spl7_27 | spl7_81)),
% 0.22/0.54    inference(subsumption_resolution,[],[f954,f264])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    l1_pre_topc(sK2) | ~spl7_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f262])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    spl7_27 <=> l1_pre_topc(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.54  fof(f954,plain,(
% 0.22/0.54    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl7_81),
% 0.22/0.54    inference(resolution,[],[f952,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.54  fof(f952,plain,(
% 0.22/0.54    ~v3_pre_topc(k2_struct_0(sK2),sK2) | spl7_81),
% 0.22/0.54    inference(avatar_component_clause,[],[f950])).
% 0.22/0.54  fof(f950,plain,(
% 0.22/0.54    spl7_81 <=> v3_pre_topc(k2_struct_0(sK2),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 0.22/0.54  fof(f953,plain,(
% 0.22/0.54    ~spl7_81 | ~spl7_27 | ~spl7_33 | ~spl7_34 | ~spl7_54 | ~spl7_66 | spl7_80),
% 0.22/0.54    inference(avatar_split_clause,[],[f948,f943,f728,f554,f363,f357,f262,f950])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    spl7_33 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.54  fof(f363,plain,(
% 0.22/0.54    spl7_34 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.54  fof(f554,plain,(
% 0.22/0.54    spl7_54 <=> m1_pre_topc(sK3,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 0.22/0.54  fof(f728,plain,(
% 0.22/0.54    spl7_66 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 0.22/0.54  fof(f943,plain,(
% 0.22/0.54    spl7_80 <=> v3_pre_topc(k2_struct_0(sK2),sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 0.22/0.54  fof(f948,plain,(
% 0.22/0.54    ~v3_pre_topc(k2_struct_0(sK2),sK2) | (~spl7_27 | ~spl7_33 | ~spl7_34 | ~spl7_54 | ~spl7_66 | spl7_80)),
% 0.22/0.54    inference(subsumption_resolution,[],[f947,f730])).
% 0.22/0.54  fof(f730,plain,(
% 0.22/0.54    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | ~spl7_66),
% 0.22/0.54    inference(avatar_component_clause,[],[f728])).
% 0.22/0.54  fof(f947,plain,(
% 0.22/0.54    ~v3_pre_topc(k2_struct_0(sK2),sK2) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | (~spl7_27 | ~spl7_33 | ~spl7_34 | ~spl7_54 | spl7_80)),
% 0.22/0.54    inference(resolution,[],[f945,f752])).
% 0.22/0.54  fof(f752,plain,(
% 0.22/0.54    ( ! [X1] : (v3_pre_topc(X1,sK3) | ~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3)))) ) | (~spl7_27 | ~spl7_33 | ~spl7_34 | ~spl7_54)),
% 0.22/0.54    inference(forward_demodulation,[],[f751,f359])).
% 0.22/0.54  fof(f359,plain,(
% 0.22/0.54    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl7_33),
% 0.22/0.54    inference(avatar_component_clause,[],[f357])).
% 0.22/0.54  fof(f751,plain,(
% 0.22/0.54    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X1,sK3)) ) | (~spl7_27 | ~spl7_34 | ~spl7_54)),
% 0.22/0.54    inference(resolution,[],[f744,f556])).
% 0.22/0.54  fof(f556,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK2) | ~spl7_54),
% 0.22/0.54    inference(avatar_component_clause,[],[f554])).
% 0.22/0.54  fof(f744,plain,(
% 0.22/0.54    ( ! [X8,X9] : (~m1_pre_topc(X9,sK2) | ~v3_pre_topc(X8,sK2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | v3_pre_topc(X8,X9)) ) | (~spl7_27 | ~spl7_34)),
% 0.22/0.54    inference(subsumption_resolution,[],[f743,f640])).
% 0.22/0.54  fof(f640,plain,(
% 0.22/0.54    ( ! [X4,X3] : (m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_pre_topc(X3,sK2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))) ) | (~spl7_27 | ~spl7_34)),
% 0.22/0.54    inference(forward_demodulation,[],[f271,f365])).
% 0.22/0.54  fof(f365,plain,(
% 0.22/0.54    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_34),
% 0.22/0.54    inference(avatar_component_clause,[],[f363])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_27),
% 0.22/0.54    inference(resolution,[],[f264,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.22/0.54  fof(f743,plain,(
% 0.22/0.54    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_pre_topc(X9,sK2) | ~v3_pre_topc(X8,sK2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | v3_pre_topc(X8,X9)) ) | (~spl7_27 | ~spl7_34)),
% 0.22/0.54    inference(forward_demodulation,[],[f274,f365])).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(X9,sK2) | ~v3_pre_topc(X8,sK2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | v3_pre_topc(X8,X9)) ) | ~spl7_27),
% 0.22/0.54    inference(resolution,[],[f264,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.22/0.54    inference(equality_resolution,[],[f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.22/0.54  fof(f945,plain,(
% 0.22/0.54    ~v3_pre_topc(k2_struct_0(sK2),sK3) | spl7_80),
% 0.22/0.54    inference(avatar_component_clause,[],[f943])).
% 0.22/0.54  fof(f946,plain,(
% 0.22/0.54    ~spl7_80 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_31 | ~spl7_33 | ~spl7_34 | ~spl7_38 | ~spl7_43 | ~spl7_46 | ~spl7_50 | ~spl7_55),
% 0.22/0.54    inference(avatar_split_clause,[],[f919,f594,f513,f482,f456,f425,f363,f357,f308,f257,f234,f215,f199,f128,f118,f113,f108,f103,f98,f93,f88,f83,f78,f943])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    spl7_1 <=> v1_funct_1(sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl7_2 <=> v2_struct_0(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl7_3 <=> v2_struct_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl7_4 <=> v2_struct_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl7_5 <=> v2_pre_topc(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl7_6 <=> l1_pre_topc(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    spl7_7 <=> v2_struct_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl7_8 <=> v2_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    spl7_9 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    spl7_11 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    spl7_18 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    spl7_21 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    spl7_24 <=> l1_pre_topc(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    spl7_26 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    spl7_31 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.54  fof(f425,plain,(
% 0.22/0.54    spl7_38 <=> m1_subset_1(sK5,k2_struct_0(sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.54  fof(f456,plain,(
% 0.22/0.54    spl7_43 <=> v2_pre_topc(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.22/0.54  fof(f482,plain,(
% 0.22/0.54    spl7_46 <=> v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.22/0.54  fof(f513,plain,(
% 0.22/0.54    spl7_50 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.22/0.54  fof(f594,plain,(
% 0.22/0.54    spl7_55 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 0.22/0.54  fof(f919,plain,(
% 0.22/0.54    ~v3_pre_topc(k2_struct_0(sK2),sK3) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_31 | ~spl7_33 | ~spl7_34 | ~spl7_38 | ~spl7_43 | ~spl7_46 | ~spl7_50 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f918,f515])).
% 0.22/0.54  fof(f515,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~spl7_50),
% 0.22/0.54    inference(avatar_component_clause,[],[f513])).
% 0.22/0.54  fof(f918,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v3_pre_topc(k2_struct_0(sK2),sK3) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_31 | ~spl7_33 | ~spl7_34 | ~spl7_38 | ~spl7_43 | ~spl7_46 | ~spl7_55)),
% 0.22/0.54    inference(forward_demodulation,[],[f917,f310])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f308])).
% 0.22/0.54  fof(f917,plain,(
% 0.22/0.54    ~v3_pre_topc(k2_struct_0(sK2),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_31 | ~spl7_33 | ~spl7_34 | ~spl7_38 | ~spl7_43 | ~spl7_46 | ~spl7_55)),
% 0.22/0.54    inference(forward_demodulation,[],[f916,f365])).
% 0.22/0.54  fof(f916,plain,(
% 0.22/0.54    ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_31 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_46 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f915,f484])).
% 0.22/0.54  fof(f484,plain,(
% 0.22/0.54    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~spl7_46),
% 0.22/0.54    inference(avatar_component_clause,[],[f482])).
% 0.22/0.54  fof(f915,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_31 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(forward_demodulation,[],[f914,f310])).
% 0.22/0.54  fof(f914,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_18 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f913,f201])).
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl7_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f199])).
% 0.22/0.54  fof(f913,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_21 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f912,f217])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f215])).
% 0.22/0.54  fof(f912,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f911,f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    v2_pre_topc(sK0) | ~spl7_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f113])).
% 0.22/0.54  fof(f911,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_9 | ~spl7_11 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f910,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ~v2_struct_0(sK0) | spl7_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f108])).
% 0.22/0.54  fof(f910,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f909,f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK0) | ~spl7_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f128])).
% 0.22/0.54  fof(f909,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f908,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ~v2_struct_0(sK2) | spl7_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f88])).
% 0.22/0.54  fof(f908,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f907,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    l1_pre_topc(sK1) | ~spl7_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f103])).
% 0.22/0.54  fof(f907,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f906,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    v2_pre_topc(sK1) | ~spl7_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f98])).
% 0.22/0.54  fof(f906,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_9 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f905,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ~v2_struct_0(sK1) | spl7_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f93])).
% 0.22/0.54  fof(f905,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_9 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f904,f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl7_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f118])).
% 0.22/0.54  fof(f904,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43 | ~spl7_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f903,f596])).
% 0.22/0.54  fof(f596,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK3) | ~spl7_55),
% 0.22/0.54    inference(avatar_component_clause,[],[f594])).
% 0.22/0.54  fof(f903,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_26 | ~spl7_33 | ~spl7_38 | ~spl7_43)),
% 0.22/0.54    inference(resolution,[],[f815,f259])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f257])).
% 0.22/0.54  fof(f815,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),sK5) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X0)) | ~m1_pre_topc(X1,sK3) | ~v3_pre_topc(u1_struct_0(X1),sK3) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0)))) | r1_tmap_1(sK3,X0,sK4,sK5)) ) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_33 | ~spl7_38 | ~spl7_43)),
% 0.22/0.54    inference(resolution,[],[f812,f427])).
% 0.22/0.54  fof(f427,plain,(
% 0.22/0.54    m1_subset_1(sK5,k2_struct_0(sK3)) | ~spl7_38),
% 0.22/0.54    inference(avatar_component_clause,[],[f425])).
% 0.22/0.54  fof(f812,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X2)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2)) | ~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f708,f393])).
% 0.22/0.54  fof(f393,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))) ) | (~spl7_24 | ~spl7_33)),
% 0.22/0.54    inference(subsumption_resolution,[],[f384,f236])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    l1_pre_topc(sK3) | ~spl7_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f234])).
% 0.22/0.54  fof(f384,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | ~spl7_33),
% 0.22/0.54    inference(superposition,[],[f62,f359])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.54  fof(f708,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X2)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2)) | ~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(forward_demodulation,[],[f707,f359])).
% 0.22/0.54  fof(f707,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X2)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2)) | ~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(forward_demodulation,[],[f706,f359])).
% 0.22/0.54  fof(f706,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(X2)) | ~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2)))) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(forward_demodulation,[],[f705,f359])).
% 0.22/0.54  fof(f705,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2)))) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | spl7_2 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f704,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ~v2_struct_0(sK3) | spl7_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f83])).
% 0.22/0.54  fof(f704,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2)))) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f703])).
% 0.22/0.54  fof(f703,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,sK3) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tmap_1(X0,X2,k3_tmap_1(X1,X2,sK3,X0,sK4),X3) | r1_tmap_1(sK3,X2,sK4,X3)) ) | (~spl7_1 | ~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(resolution,[],[f692,f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_tsep_1(X2,X3) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | ~spl7_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f137,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | ~spl7_1),
% 0.22/0.54    inference(resolution,[],[f80,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.22/0.54    inference(equality_resolution,[],[f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    v1_funct_1(sK4) | ~spl7_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f78])).
% 0.22/0.54  fof(f692,plain,(
% 0.22/0.54    ( ! [X10] : (v1_tsep_1(X10,sK3) | ~m1_pre_topc(X10,sK3) | ~v3_pre_topc(u1_struct_0(X10),sK3) | ~m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(k2_struct_0(sK3)))) ) | (~spl7_24 | ~spl7_33 | ~spl7_43)),
% 0.22/0.54    inference(forward_demodulation,[],[f691,f359])).
% 0.22/0.54  fof(f691,plain,(
% 0.22/0.54    ( ! [X10] : (~m1_pre_topc(X10,sK3) | ~m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X10),sK3) | v1_tsep_1(X10,sK3)) ) | (~spl7_24 | ~spl7_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f247,f457])).
% 0.22/0.54  fof(f457,plain,(
% 0.22/0.54    v2_pre_topc(sK3) | ~spl7_43),
% 0.22/0.54    inference(avatar_component_clause,[],[f456])).
% 0.22/0.54  fof(f247,plain,(
% 0.22/0.54    ( ! [X10] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X10,sK3) | ~m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X10),sK3) | v1_tsep_1(X10,sK3)) ) | ~spl7_24),
% 0.22/0.54    inference(resolution,[],[f236,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.54  fof(f731,plain,(
% 0.22/0.54    spl7_66 | ~spl7_24 | ~spl7_33 | ~spl7_34 | ~spl7_55),
% 0.22/0.54    inference(avatar_split_clause,[],[f712,f594,f363,f357,f234,f728])).
% 0.22/0.54  fof(f712,plain,(
% 0.22/0.54    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | (~spl7_24 | ~spl7_33 | ~spl7_34 | ~spl7_55)),
% 0.22/0.54    inference(forward_demodulation,[],[f710,f365])).
% 0.22/0.54  fof(f710,plain,(
% 0.22/0.54    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | (~spl7_24 | ~spl7_33 | ~spl7_55)),
% 0.22/0.54    inference(resolution,[],[f393,f596])).
% 0.22/0.54  fof(f597,plain,(
% 0.22/0.54    spl7_55 | ~spl7_22 | ~spl7_27 | ~spl7_30),
% 0.22/0.54    inference(avatar_split_clause,[],[f592,f297,f262,f221,f594])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    spl7_22 <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    spl7_30 <=> m1_pre_topc(sK2,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.54  fof(f592,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK3) | (~spl7_22 | ~spl7_27 | ~spl7_30)),
% 0.22/0.54    inference(forward_demodulation,[],[f591,f223])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl7_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f221])).
% 0.22/0.54  fof(f591,plain,(
% 0.22/0.54    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl7_27 | ~spl7_30)),
% 0.22/0.54    inference(subsumption_resolution,[],[f584,f264])).
% 0.22/0.54  fof(f584,plain,(
% 0.22/0.54    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | (~spl7_27 | ~spl7_30)),
% 0.22/0.54    inference(resolution,[],[f269,f299])).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK2) | ~spl7_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f297])).
% 0.22/0.54  fof(f269,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_pre_topc(sK2,X1) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1)) ) | ~spl7_27),
% 0.22/0.54    inference(resolution,[],[f264,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.54  fof(f557,plain,(
% 0.22/0.54    spl7_54 | ~spl7_22 | ~spl7_24 | ~spl7_27 | ~spl7_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f552,f288,f262,f234,f221,f554])).
% 0.22/0.54  fof(f288,plain,(
% 0.22/0.54    spl7_29 <=> m1_pre_topc(sK3,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.54  fof(f552,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK2) | (~spl7_22 | ~spl7_24 | ~spl7_27 | ~spl7_29)),
% 0.22/0.54    inference(subsumption_resolution,[],[f551,f290])).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK3) | ~spl7_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f288])).
% 0.22/0.54  fof(f551,plain,(
% 0.22/0.54    ~m1_pre_topc(sK3,sK3) | m1_pre_topc(sK3,sK2) | (~spl7_22 | ~spl7_24 | ~spl7_27)),
% 0.22/0.54    inference(forward_demodulation,[],[f548,f223])).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    ~m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(sK3,sK2) | (~spl7_24 | ~spl7_27)),
% 0.22/0.54    inference(resolution,[],[f240,f264])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(sK3,X0)) ) | ~spl7_24),
% 0.22/0.54    inference(resolution,[],[f236,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f516,plain,(
% 0.22/0.54    spl7_50 | ~spl7_23 | ~spl7_31 | ~spl7_33),
% 0.22/0.54    inference(avatar_split_clause,[],[f486,f357,f308,f229,f513])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    spl7_23 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.54  fof(f486,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | (~spl7_23 | ~spl7_31 | ~spl7_33)),
% 0.22/0.54    inference(forward_demodulation,[],[f318,f359])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | (~spl7_23 | ~spl7_31)),
% 0.22/0.54    inference(superposition,[],[f231,f310])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl7_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f229])).
% 0.22/0.54  fof(f485,plain,(
% 0.22/0.54    spl7_46 | ~spl7_20 | ~spl7_31 | ~spl7_33),
% 0.22/0.54    inference(avatar_split_clause,[],[f480,f357,f308,f210,f482])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    spl7_20 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.54  fof(f480,plain,(
% 0.22/0.54    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | (~spl7_20 | ~spl7_31 | ~spl7_33)),
% 0.22/0.54    inference(forward_demodulation,[],[f319,f359])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | (~spl7_20 | ~spl7_31)),
% 0.22/0.54    inference(superposition,[],[f212,f310])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl7_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f210])).
% 0.22/0.54  fof(f479,plain,(
% 0.22/0.54    ~spl7_8 | ~spl7_9 | ~spl7_12 | spl7_45),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f478])).
% 0.22/0.54  fof(f478,plain,(
% 0.22/0.54    $false | (~spl7_8 | ~spl7_9 | ~spl7_12 | spl7_45)),
% 0.22/0.54    inference(subsumption_resolution,[],[f476,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK0) | ~spl7_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    spl7_12 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.54  fof(f476,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK0) | (~spl7_8 | ~spl7_9 | spl7_45)),
% 0.22/0.54    inference(resolution,[],[f473,f167])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X5] : (v2_pre_topc(X5) | ~m1_pre_topc(X5,sK0)) ) | (~spl7_8 | ~spl7_9)),
% 0.22/0.54    inference(subsumption_resolution,[],[f162,f115])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X5] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X5,sK0) | v2_pre_topc(X5)) ) | ~spl7_9),
% 0.22/0.54    inference(resolution,[],[f120,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.54  fof(f473,plain,(
% 0.22/0.54    ~v2_pre_topc(sK2) | spl7_45),
% 0.22/0.54    inference(avatar_component_clause,[],[f471])).
% 0.22/0.54  fof(f466,plain,(
% 0.22/0.54    ~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_43),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f465])).
% 0.22/0.54  fof(f465,plain,(
% 0.22/0.54    $false | (~spl7_8 | ~spl7_9 | ~spl7_11 | spl7_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f463,f130])).
% 0.22/0.54  fof(f463,plain,(
% 0.22/0.54    ~m1_pre_topc(sK3,sK0) | (~spl7_8 | ~spl7_9 | spl7_43)),
% 0.22/0.54    inference(resolution,[],[f458,f167])).
% 0.22/0.54  fof(f458,plain,(
% 0.22/0.54    ~v2_pre_topc(sK3) | spl7_43),
% 0.22/0.54    inference(avatar_component_clause,[],[f456])).
% 0.22/0.54  fof(f428,plain,(
% 0.22/0.54    spl7_38 | ~spl7_16 | ~spl7_33),
% 0.22/0.54    inference(avatar_split_clause,[],[f383,f357,f187,f425])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.54  fof(f383,plain,(
% 0.22/0.54    m1_subset_1(sK5,k2_struct_0(sK3)) | (~spl7_16 | ~spl7_33)),
% 0.22/0.54    inference(superposition,[],[f189,f359])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f187])).
% 0.22/0.54  fof(f366,plain,(
% 0.22/0.54    spl7_34 | ~spl7_28),
% 0.22/0.54    inference(avatar_split_clause,[],[f283,f278,f363])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    spl7_28 <=> l1_struct_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.54  fof(f283,plain,(
% 0.22/0.54    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_28),
% 0.22/0.54    inference(resolution,[],[f280,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f280,plain,(
% 0.22/0.54    l1_struct_0(sK2) | ~spl7_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f278])).
% 0.22/0.54  fof(f360,plain,(
% 0.22/0.54    spl7_33 | ~spl7_25),
% 0.22/0.54    inference(avatar_split_clause,[],[f255,f250,f357])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    spl7_25 <=> l1_struct_0(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl7_25),
% 0.22/0.54    inference(resolution,[],[f252,f56])).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    l1_struct_0(sK3) | ~spl7_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f250])).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    spl7_31 | ~spl7_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f191,f172,f308])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl7_13 <=> l1_struct_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_13),
% 0.22/0.54    inference(resolution,[],[f174,f56])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    l1_struct_0(sK1) | ~spl7_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f172])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    spl7_30 | ~spl7_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f267,f262,f297])).
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK2) | ~spl7_27),
% 0.22/0.54    inference(resolution,[],[f264,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.54  fof(f291,plain,(
% 0.22/0.54    spl7_29 | ~spl7_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f239,f234,f288])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK3) | ~spl7_24),
% 0.22/0.54    inference(resolution,[],[f236,f58])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    spl7_28 | ~spl7_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f266,f262,f278])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    l1_struct_0(sK2) | ~spl7_27),
% 0.22/0.54    inference(resolution,[],[f264,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    spl7_27 | ~spl7_9 | ~spl7_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f226,f133,f118,f262])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    l1_pre_topc(sK2) | (~spl7_9 | ~spl7_12)),
% 0.22/0.54    inference(resolution,[],[f160,f135])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | l1_pre_topc(X2)) ) | ~spl7_9),
% 0.22/0.54    inference(resolution,[],[f120,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    spl7_26 | ~spl7_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f254,f123,f257])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    spl7_10 <=> sK5 = sK6),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_10),
% 0.22/0.54    inference(forward_demodulation,[],[f39,f125])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    sK5 = sK6 | ~spl7_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f123])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f14])).
% 0.22/0.54  fof(f14,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    spl7_25 | ~spl7_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f238,f234,f250])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    l1_struct_0(sK3) | ~spl7_24),
% 0.22/0.54    inference(resolution,[],[f236,f57])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    spl7_24 | ~spl7_9 | ~spl7_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f225,f128,f118,f234])).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    l1_pre_topc(sK3) | (~spl7_9 | ~spl7_11)),
% 0.22/0.54    inference(resolution,[],[f160,f130])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    spl7_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f229])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    spl7_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f221])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    spl7_21 | ~spl7_10 | ~spl7_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f208,f177,f123,f215])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl7_14 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl7_10 | ~spl7_14)),
% 0.22/0.54    inference(forward_demodulation,[],[f179,f125])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl7_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f177])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    spl7_20),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f210])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    ~spl7_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f199])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    spl7_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f187])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    spl7_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f37,f177])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    spl7_13 | ~spl7_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f141,f103,f172])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    l1_struct_0(sK1) | ~spl7_6),
% 0.22/0.54    inference(resolution,[],[f105,f57])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl7_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f49,f133])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    spl7_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f128])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    spl7_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f123])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    sK5 = sK6),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl7_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f118])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl7_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f54,f113])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ~spl7_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f53,f108])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl7_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f103])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    l1_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f51,f98])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    v2_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ~spl7_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f50,f93])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ~spl7_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f88])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ~v2_struct_0(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~spl7_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f83])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ~v2_struct_0(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl7_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f78])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v1_funct_1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (22551)------------------------------
% 0.22/0.54  % (22551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22551)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (22551)Memory used [KB]: 11257
% 0.22/0.54  % (22551)Time elapsed: 0.103 s
% 0.22/0.54  % (22551)------------------------------
% 0.22/0.54  % (22551)------------------------------
% 0.22/0.54  % (22570)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % (22564)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (22544)Success in time 0.184 s
%------------------------------------------------------------------------------
