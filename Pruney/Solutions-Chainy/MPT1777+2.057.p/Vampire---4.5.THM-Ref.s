%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  262 ( 679 expanded)
%              Number of leaves         :   66 ( 364 expanded)
%              Depth                    :   20
%              Number of atoms          : 1521 (6250 expanded)
%              Number of equality atoms :   90 ( 755 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f653,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f175,f188,f260,f274,f278,f281,f287,f291,f313,f315,f356,f370,f376,f383,f385,f387,f407,f440,f466,f470,f477,f616,f623,f635,f646,f652])).

fof(f652,plain,
    ( spl7_19
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f649,f630,f173,f164,f160,f140,f132,f168])).

fof(f168,plain,
    ( spl7_19
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f132,plain,
    ( spl7_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f140,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f160,plain,
    ( spl7_17
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f164,plain,
    ( spl7_18
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f173,plain,
    ( spl7_20
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f630,plain,
    ( spl7_84
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

% (8896)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f649,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_20
    | ~ spl7_84 ),
    inference(resolution,[],[f631,f174])).

fof(f174,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f631,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f630])).

fof(f646,plain,
    ( ~ spl7_55
    | spl7_85 ),
    inference(avatar_split_clause,[],[f644,f633,f374])).

fof(f374,plain,
    ( spl7_55
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f633,plain,
    ( spl7_85
  <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f644,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl7_85 ),
    inference(resolution,[],[f634,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f634,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
    | spl7_85 ),
    inference(avatar_component_clause,[],[f633])).

fof(f635,plain,
    ( spl7_13
    | spl7_84
    | ~ spl7_54
    | ~ spl7_85
    | ~ spl7_41
    | ~ spl7_60
    | ~ spl7_83 ),
    inference(avatar_split_clause,[],[f628,f620,f405,f289,f633,f366,f630,f144])).

fof(f144,plain,
    ( spl7_13
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f366,plain,
    ( spl7_54
  <=> m1_subset_1(sK5,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f289,plain,
    ( spl7_41
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f405,plain,
    ( spl7_60
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f620,plain,
    ( spl7_83
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(X1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f628,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_41
    | ~ spl7_60
    | ~ spl7_83 ),
    inference(forward_demodulation,[],[f627,f290])).

fof(f290,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f289])).

fof(f627,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_41
    | ~ spl7_60
    | ~ spl7_83 ),
    inference(forward_demodulation,[],[f624,f290])).

fof(f624,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_60
    | ~ spl7_83 ),
    inference(resolution,[],[f621,f406])).

fof(f406,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f405])).

fof(f621,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(X1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f620])).

fof(f623,plain,
    ( ~ spl7_70
    | spl7_83
    | spl7_57
    | ~ spl7_54
    | ~ spl7_55
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f617,f612,f374,f366,f381,f620,f475])).

fof(f475,plain,
    ( spl7_70
  <=> v3_pre_topc(k2_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f381,plain,
    ( spl7_57
  <=> v1_xboole_0(k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f612,plain,
    ( spl7_82
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,X2)
        | v1_xboole_0(X2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f617,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | v1_xboole_0(k2_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(X1))
        | ~ v3_pre_topc(k2_struct_0(sK2),sK3)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1)) )
    | ~ spl7_55
    | ~ spl7_82 ),
    inference(resolution,[],[f613,f375])).

fof(f375,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f374])).

fof(f613,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,X2)
        | v1_xboole_0(X2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0)) )
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f612])).

fof(f616,plain,
    ( spl7_16
    | ~ spl7_15
    | ~ spl7_14
    | spl7_11
    | ~ spl7_54
    | spl7_82
    | ~ spl7_68
    | ~ spl7_69
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f609,f438,f285,f186,f128,f96,f468,f464,f612,f366,f136,f148,f152,f156])).

fof(f156,plain,
    ( spl7_16
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f152,plain,
    ( spl7_15
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f148,plain,
    ( spl7_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f136,plain,
    ( spl7_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f464,plain,
    ( spl7_68
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f468,plain,
    ( spl7_69
  <=> v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f96,plain,
    ( spl7_1
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f128,plain,
    ( spl7_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f186,plain,
    ( spl7_22
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f285,plain,
    ( spl7_40
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f438,plain,
    ( spl7_64
  <=> k2_struct_0(sK3) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f609,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f608,f439])).

fof(f439,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK2)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f438])).

fof(f608,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f607,f286])).

% (8916)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f286,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f607,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f606,f187])).

% (8905)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f187,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f606,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f605,f439])).

fof(f605,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f604,f286])).

fof(f604,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_22
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f603,f187])).

fof(f603,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f602,f439])).

fof(f602,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f601,f286])).

fof(f601,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_40
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f600,f439])).

fof(f600,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k2_struct_0(sK3))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f599,f286])).

fof(f599,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK5,X2) )
    | spl7_1
    | ~ spl7_9 ),
    inference(resolution,[],[f598,f97])).

fof(f97,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f598,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( r1_tmap_1(X4,X2,sK4,X5)
        | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,sK4),X5)
        | ~ v3_pre_topc(X0,X4)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_pre_topc(X1,X4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X4),u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X1,X3)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X5,X0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f543,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f543,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r2_hidden(X4,X5)
        | ~ r1_tarski(X5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
        | ~ v3_pre_topc(X5,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X0))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_9 ),
    inference(resolution,[],[f93,f129])).

fof(f129,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f93,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f477,plain,
    ( ~ spl7_39
    | ~ spl7_46
    | spl7_70
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f462,f438,f475,f322,f276])).

fof(f276,plain,
    ( spl7_39
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f322,plain,
    ( spl7_46
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f462,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl7_64 ),
    inference(superposition,[],[f85,f439])).

fof(f85,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f470,plain,
    ( spl7_69
    | ~ spl7_44
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f456,f438,f309,f468])).

fof(f309,plain,
    ( spl7_44
  <=> v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f456,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
    | ~ spl7_44
    | ~ spl7_64 ),
    inference(superposition,[],[f310,f439])).

fof(f310,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f309])).

fof(f466,plain,
    ( spl7_68
    | ~ spl7_43
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f455,f438,f305,f464])).

fof(f305,plain,
    ( spl7_43
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f455,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | ~ spl7_43
    | ~ spl7_64 ),
    inference(superposition,[],[f306,f439])).

fof(f306,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f305])).

fof(f440,plain,
    ( spl7_19
    | ~ spl7_17
    | spl7_13
    | ~ spl7_12
    | ~ spl7_36
    | ~ spl7_10
    | spl7_11
    | spl7_64
    | ~ spl7_40
    | ~ spl7_41
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f434,f354,f289,f285,f438,f136,f132,f258,f140,f144,f160,f168])).

fof(f258,plain,
    ( spl7_36
  <=> v1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f354,plain,
    ( spl7_53
  <=> sK3 = k1_tsep_1(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f434,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_40
    | ~ spl7_41
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f433,f290])).

fof(f433,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_40
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f432,f286])).

fof(f432,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f431,f89])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f431,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_53 ),
    inference(duplicate_literal_removal,[],[f428])).

fof(f428,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_53 ),
    inference(superposition,[],[f92,f355])).

fof(f355,plain,
    ( sK3 = k1_tsep_1(sK0,sK2,sK2)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f354])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f407,plain,
    ( spl7_19
    | ~ spl7_18
    | ~ spl7_17
    | spl7_13
    | ~ spl7_12
    | spl7_60
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f402,f354,f405,f140,f144,f160,f164,f168])).

fof(f402,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_53 ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_53 ),
    inference(superposition,[],[f84,f355])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f387,plain,
    ( ~ spl7_17
    | ~ spl7_10
    | spl7_46 ),
    inference(avatar_split_clause,[],[f386,f322,f132,f160])).

fof(f386,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_10
    | spl7_46 ),
    inference(resolution,[],[f357,f133])).

fof(f133,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_46 ),
    inference(resolution,[],[f323,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f323,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f322])).

fof(f385,plain,
    ( ~ spl7_35
    | spl7_56 ),
    inference(avatar_split_clause,[],[f384,f378,f255])).

fof(f255,plain,
    ( spl7_35
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f378,plain,
    ( spl7_56
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f384,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_56 ),
    inference(resolution,[],[f379,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f379,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_56 ),
    inference(avatar_component_clause,[],[f378])).

fof(f383,plain,
    ( spl7_13
    | ~ spl7_56
    | ~ spl7_57
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f364,f289,f381,f378,f144])).

fof(f364,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_41 ),
    inference(superposition,[],[f78,f290])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f376,plain,
    ( ~ spl7_35
    | spl7_55
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f363,f289,f374,f255])).

fof(f363,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_41 ),
    inference(superposition,[],[f227,f290])).

fof(f227,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f75,f76])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f370,plain,
    ( spl7_54
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f369,f289,f108,f104,f366])).

fof(f104,plain,
    ( spl7_3
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f108,plain,
    ( spl7_4
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f369,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_41 ),
    inference(forward_demodulation,[],[f360,f105])).

fof(f105,plain,
    ( sK5 = sK6
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f360,plain,
    ( m1_subset_1(sK6,k2_struct_0(sK2))
    | ~ spl7_4
    | ~ spl7_41 ),
    inference(superposition,[],[f109,f290])).

fof(f109,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f356,plain,
    ( spl7_19
    | ~ spl7_18
    | ~ spl7_17
    | spl7_13
    | spl7_53
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f351,f140,f116,f354,f144,f160,f164,f168])).

fof(f116,plain,
    ( spl7_6
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f351,plain,
    ( sK3 = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f345,f117])).

fof(f117,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f345,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f83,f141])).

fof(f141,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f315,plain,
    ( spl7_44
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f314,f285,f186,f124,f309])).

fof(f124,plain,
    ( spl7_8
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f314,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f298,f187])).

fof(f298,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_40 ),
    inference(superposition,[],[f125,f286])).

fof(f125,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f313,plain,
    ( spl7_43
    | ~ spl7_7
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f312,f285,f186,f120,f305])).

fof(f120,plain,
    ( spl7_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f312,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_7
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f297,f187])).

fof(f297,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_7
    | ~ spl7_40 ),
    inference(superposition,[],[f121,f286])).

fof(f121,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f291,plain,
    ( ~ spl7_17
    | spl7_41
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f283,f140,f289,f160])).

fof(f283,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f184,f141])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f181,f77])).

fof(f181,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f74,f76])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f287,plain,
    ( ~ spl7_17
    | spl7_40
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f282,f132,f285,f160])).

% (8899)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f282,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f184,f133])).

fof(f281,plain,
    ( ~ spl7_17
    | ~ spl7_12
    | spl7_35 ),
    inference(avatar_split_clause,[],[f280,f255,f140,f160])).

fof(f280,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_12
    | spl7_35 ),
    inference(resolution,[],[f279,f141])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_35 ),
    inference(resolution,[],[f256,f77])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_35 ),
    inference(avatar_component_clause,[],[f255])).

fof(f278,plain,
    ( ~ spl7_34
    | ~ spl7_35
    | spl7_39
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f264,f116,f276,f255,f252])).

fof(f252,plain,
    ( spl7_34
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f264,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_6 ),
    inference(superposition,[],[f87,f117])).

fof(f87,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f274,plain,
    ( ~ spl7_18
    | ~ spl7_17
    | ~ spl7_12
    | spl7_34 ),
    inference(avatar_split_clause,[],[f273,f252,f140,f160,f164])).

fof(f273,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_12
    | spl7_34 ),
    inference(resolution,[],[f261,f141])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl7_34 ),
    inference(resolution,[],[f253,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f253,plain,
    ( ~ v2_pre_topc(sK2)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f252])).

fof(f260,plain,
    ( ~ spl7_34
    | ~ spl7_35
    | spl7_36
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f240,f116,f258,f255,f252])).

fof(f240,plain,
    ( v1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_6 ),
    inference(superposition,[],[f86,f117])).

fof(f86,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f188,plain,
    ( spl7_22
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f182,f148,f186])).

fof(f182,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f181,f149])).

fof(f149,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f175,plain,
    ( spl7_20
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f171,f104,f100,f173])).

fof(f100,plain,
    ( spl7_2
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f171,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f101,f105])).

fof(f101,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f170,plain,(
    ~ spl7_19 ),
    inference(avatar_split_clause,[],[f55,f168])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f51,f50,f49,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK1,X4,X5)
                          & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK1,X4,X5)
                        & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK1,X4,X5)
                      & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK1,X4,X5)
                    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK3,sK1,X4,X5)
                  & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK3,sK1,X4,X5)
                & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK3,sK1,sK4,X5)
              & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK3,sK1,sK4,X5)
            & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
          & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
        & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
      & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f166,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f56,f164])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f162,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f57,f160])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f158,plain,(
    ~ spl7_16 ),
    inference(avatar_split_clause,[],[f58,f156])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f154,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f59,f152])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f150,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f60,f148])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f146,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f61,f144])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f142,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f62,f140])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f138,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f63,f136])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f134,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f64,f132])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f65,f128])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f66,f124])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f67,f120])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f118,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f68,f116])).

fof(f68,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f70,f108])).

% (8906)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f71,f104])).

fof(f71,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f72,f100])).

fof(f72,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f98,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f73,f96])).

fof(f73,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (8910)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (8901)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (8913)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (8895)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (8900)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8904)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8907)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8897)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (8901)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f653,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f175,f188,f260,f274,f278,f281,f287,f291,f313,f315,f356,f370,f376,f383,f385,f387,f407,f440,f466,f470,f477,f616,f623,f635,f646,f652])).
% 0.21/0.49  fof(f652,plain,(
% 0.21/0.49    spl7_19 | ~spl7_10 | ~spl7_12 | ~spl7_17 | ~spl7_18 | ~spl7_20 | ~spl7_84),
% 0.21/0.49    inference(avatar_split_clause,[],[f649,f630,f173,f164,f160,f140,f132,f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl7_19 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl7_10 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl7_12 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl7_17 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl7_18 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl7_20 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.49  fof(f630,plain,(
% 0.21/0.49    spl7_84 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 0.21/0.49  % (8896)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f649,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | (~spl7_20 | ~spl7_84)),
% 0.21/0.49    inference(resolution,[],[f631,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f173])).
% 0.21/0.49  fof(f631,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | ~spl7_84),
% 0.21/0.49    inference(avatar_component_clause,[],[f630])).
% 0.21/0.49  fof(f646,plain,(
% 0.21/0.49    ~spl7_55 | spl7_85),
% 0.21/0.49    inference(avatar_split_clause,[],[f644,f633,f374])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    spl7_55 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 0.21/0.49  fof(f633,plain,(
% 0.21/0.49    spl7_85 <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 0.21/0.49  fof(f644,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | spl7_85),
% 0.21/0.49    inference(resolution,[],[f634,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f634,plain,(
% 0.21/0.49    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) | spl7_85),
% 0.21/0.49    inference(avatar_component_clause,[],[f633])).
% 0.21/0.49  fof(f635,plain,(
% 0.21/0.49    spl7_13 | spl7_84 | ~spl7_54 | ~spl7_85 | ~spl7_41 | ~spl7_60 | ~spl7_83),
% 0.21/0.49    inference(avatar_split_clause,[],[f628,f620,f405,f289,f633,f366,f630,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl7_13 <=> v2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    spl7_54 <=> m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    spl7_41 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.49  fof(f405,plain,(
% 0.21/0.49    spl7_60 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.21/0.49  fof(f620,plain,(
% 0.21/0.49    spl7_83 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~r1_tarski(k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).
% 0.21/0.49  fof(f628,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | v2_struct_0(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl7_41 | ~spl7_60 | ~spl7_83)),
% 0.21/0.49    inference(forward_demodulation,[],[f627,f290])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f289])).
% 0.21/0.49  fof(f627,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | v2_struct_0(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl7_41 | ~spl7_60 | ~spl7_83)),
% 0.21/0.49    inference(forward_demodulation,[],[f624,f290])).
% 0.21/0.49  fof(f624,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl7_60 | ~spl7_83)),
% 0.21/0.49    inference(resolution,[],[f621,f406])).
% 0.21/0.49  fof(f406,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3) | ~spl7_60),
% 0.21/0.49    inference(avatar_component_clause,[],[f405])).
% 0.21/0.49  fof(f621,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~r1_tarski(k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_83),
% 0.21/0.49    inference(avatar_component_clause,[],[f620])).
% 0.21/0.49  fof(f623,plain,(
% 0.21/0.49    ~spl7_70 | spl7_83 | spl7_57 | ~spl7_54 | ~spl7_55 | ~spl7_82),
% 0.21/0.49    inference(avatar_split_clause,[],[f617,f612,f374,f366,f381,f620,f475])).
% 0.21/0.49  fof(f475,plain,(
% 0.21/0.49    spl7_70 <=> v3_pre_topc(k2_struct_0(sK2),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    spl7_57 <=> v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 0.21/0.49  fof(f612,plain,(
% 0.21/0.49    spl7_82 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,X2) | v1_xboole_0(X2) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~r1_tarski(X2,u1_struct_0(X0)) | ~v3_pre_topc(X2,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 0.21/0.49  fof(f617,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | v1_xboole_0(k2_struct_0(sK2)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(k2_struct_0(sK2),u1_struct_0(X1)) | ~v3_pre_topc(k2_struct_0(sK2),sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1))) ) | (~spl7_55 | ~spl7_82)),
% 0.21/0.49    inference(resolution,[],[f613,f375])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~spl7_55),
% 0.21/0.49    inference(avatar_component_clause,[],[f374])).
% 0.21/0.49  fof(f613,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,X2) | v1_xboole_0(X2) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~r1_tarski(X2,u1_struct_0(X0)) | ~v3_pre_topc(X2,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0))) ) | ~spl7_82),
% 0.21/0.49    inference(avatar_component_clause,[],[f612])).
% 0.21/0.49  fof(f616,plain,(
% 0.21/0.49    spl7_16 | ~spl7_15 | ~spl7_14 | spl7_11 | ~spl7_54 | spl7_82 | ~spl7_68 | ~spl7_69 | spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64),
% 0.21/0.49    inference(avatar_split_clause,[],[f609,f438,f285,f186,f128,f96,f468,f464,f612,f366,f136,f148,f152,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl7_16 <=> v2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl7_15 <=> v2_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl7_14 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl7_11 <=> v2_struct_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.49  fof(f464,plain,(
% 0.21/0.49    spl7_68 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    spl7_69 <=> v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl7_1 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl7_9 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl7_22 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    spl7_40 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    spl7_64 <=> k2_struct_0(sK3) = k2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.21/0.49  fof(f609,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f608,f439])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    k2_struct_0(sK3) = k2_struct_0(sK2) | ~spl7_64),
% 0.21/0.49    inference(avatar_component_clause,[],[f438])).
% 0.21/0.49  fof(f608,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f607,f286])).
% 0.21/0.49  % (8916)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl7_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f285])).
% 0.21/0.49  fof(f607,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f606,f187])).
% 0.21/0.49  % (8905)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f606,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f605,f439])).
% 0.21/0.49  fof(f605,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f604,f286])).
% 0.21/0.49  fof(f604,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_22 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f603,f187])).
% 0.21/0.49  fof(f603,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f602,f439])).
% 0.21/0.49  fof(f602,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f601,f286])).
% 0.21/0.49  fof(f601,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_40 | ~spl7_64)),
% 0.21/0.49    inference(forward_demodulation,[],[f600,f439])).
% 0.21/0.49  fof(f600,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k2_struct_0(sK3)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9 | ~spl7_40)),
% 0.21/0.49    inference(forward_demodulation,[],[f599,f286])).
% 0.21/0.49  fof(f599,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(sK5,X2)) ) | (spl7_1 | ~spl7_9)),
% 0.21/0.49    inference(resolution,[],[f598,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f598,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X4,X2,sK4,X5) | ~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,sK4),X5) | ~v3_pre_topc(X0,X4) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X4))) | ~m1_pre_topc(X1,X4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X4),u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X1)) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(X1,X3) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v1_xboole_0(X0) | ~m1_subset_1(X5,X0)) ) | ~spl7_9),
% 0.21/0.49    inference(resolution,[],[f543,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f543,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X5) | ~r1_tarski(X5,u1_struct_0(X0)) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl7_9),
% 0.21/0.49    inference(resolution,[],[f93,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl7_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.21/0.49  fof(f477,plain,(
% 0.21/0.49    ~spl7_39 | ~spl7_46 | spl7_70 | ~spl7_64),
% 0.21/0.49    inference(avatar_split_clause,[],[f462,f438,f475,f322,f276])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl7_39 <=> v2_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    spl7_46 <=> l1_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    v3_pre_topc(k2_struct_0(sK2),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl7_64),
% 0.21/0.49    inference(superposition,[],[f85,f439])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.49  fof(f470,plain,(
% 0.21/0.49    spl7_69 | ~spl7_44 | ~spl7_64),
% 0.21/0.49    inference(avatar_split_clause,[],[f456,f438,f309,f468])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    spl7_44 <=> v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.49  fof(f456,plain,(
% 0.21/0.49    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | (~spl7_44 | ~spl7_64)),
% 0.21/0.49    inference(superposition,[],[f310,f439])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~spl7_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f309])).
% 0.21/0.49  fof(f466,plain,(
% 0.21/0.49    spl7_68 | ~spl7_43 | ~spl7_64),
% 0.21/0.49    inference(avatar_split_clause,[],[f455,f438,f305,f464])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    spl7_43 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.49  fof(f455,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | (~spl7_43 | ~spl7_64)),
% 0.21/0.49    inference(superposition,[],[f306,f439])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~spl7_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f305])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    spl7_19 | ~spl7_17 | spl7_13 | ~spl7_12 | ~spl7_36 | ~spl7_10 | spl7_11 | spl7_64 | ~spl7_40 | ~spl7_41 | ~spl7_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f434,f354,f289,f285,f438,f136,f132,f258,f140,f144,f160,f168])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    spl7_36 <=> v1_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    spl7_53 <=> sK3 = k1_tsep_1(sK0,sK2,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    k2_struct_0(sK3) = k2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_40 | ~spl7_41 | ~spl7_53)),
% 0.21/0.49    inference(forward_demodulation,[],[f433,f290])).
% 0.21/0.49  fof(f433,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_struct_0(sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_40 | ~spl7_53)),
% 0.21/0.49    inference(forward_demodulation,[],[f432,f286])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    u1_struct_0(sK2) = u1_struct_0(sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_53),
% 0.21/0.49    inference(forward_demodulation,[],[f431,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    inference(rectify,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_pre_topc(sK3) | u1_struct_0(sK3) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_53),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f428])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_pre_topc(sK3) | u1_struct_0(sK3) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_53),
% 0.21/0.49    inference(superposition,[],[f92,f355])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    sK3 = k1_tsep_1(sK0,sK2,sK2) | ~spl7_53),
% 0.21/0.49    inference(avatar_component_clause,[],[f354])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    spl7_19 | ~spl7_18 | ~spl7_17 | spl7_13 | ~spl7_12 | spl7_60 | ~spl7_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f402,f354,f405,f140,f144,f160,f164,f168])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_53),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f401])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_53),
% 0.21/0.49    inference(superposition,[],[f84,f355])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    ~spl7_17 | ~spl7_10 | spl7_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f386,f322,f132,f160])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | (~spl7_10 | spl7_46)),
% 0.21/0.49    inference(resolution,[],[f357,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0) | ~spl7_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl7_46),
% 0.21/0.49    inference(resolution,[],[f323,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ~l1_pre_topc(sK3) | spl7_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f322])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~spl7_35 | spl7_56),
% 0.21/0.49    inference(avatar_split_clause,[],[f384,f378,f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl7_35 <=> l1_pre_topc(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    spl7_56 <=> l1_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    ~l1_pre_topc(sK2) | spl7_56),
% 0.21/0.49    inference(resolution,[],[f379,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    ~l1_struct_0(sK2) | spl7_56),
% 0.21/0.49    inference(avatar_component_clause,[],[f378])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    spl7_13 | ~spl7_56 | ~spl7_57 | ~spl7_41),
% 0.21/0.49    inference(avatar_split_clause,[],[f364,f289,f381,f378,f144])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_41),
% 0.21/0.49    inference(superposition,[],[f78,f290])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    ~spl7_35 | spl7_55 | ~spl7_41),
% 0.21/0.49    inference(avatar_split_clause,[],[f363,f289,f374,f255])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~spl7_41),
% 0.21/0.49    inference(superposition,[],[f227,f290])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f75,f76])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    spl7_54 | ~spl7_3 | ~spl7_4 | ~spl7_41),
% 0.21/0.49    inference(avatar_split_clause,[],[f369,f289,f108,f104,f366])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl7_3 <=> sK5 = sK6),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl7_4 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    m1_subset_1(sK5,k2_struct_0(sK2)) | (~spl7_3 | ~spl7_4 | ~spl7_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f360,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    sK5 = sK6 | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    m1_subset_1(sK6,k2_struct_0(sK2)) | (~spl7_4 | ~spl7_41)),
% 0.21/0.49    inference(superposition,[],[f109,f290])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    spl7_19 | ~spl7_18 | ~spl7_17 | spl7_13 | spl7_53 | ~spl7_6 | ~spl7_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f351,f140,f116,f354,f144,f160,f164,f168])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl7_6 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    sK3 = k1_tsep_1(sK0,sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_6 | ~spl7_12)),
% 0.21/0.49    inference(forward_demodulation,[],[f345,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_12),
% 0.21/0.49    inference(resolution,[],[f83,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0) | ~spl7_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    spl7_44 | ~spl7_8 | ~spl7_22 | ~spl7_40),
% 0.21/0.50    inference(avatar_split_clause,[],[f314,f285,f186,f124,f309])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl7_8 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | (~spl7_8 | ~spl7_22 | ~spl7_40)),
% 0.21/0.50    inference(forward_demodulation,[],[f298,f187])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | (~spl7_8 | ~spl7_40)),
% 0.21/0.50    inference(superposition,[],[f125,f286])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl7_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    spl7_43 | ~spl7_7 | ~spl7_22 | ~spl7_40),
% 0.21/0.50    inference(avatar_split_clause,[],[f312,f285,f186,f120,f305])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl7_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | (~spl7_7 | ~spl7_22 | ~spl7_40)),
% 0.21/0.50    inference(forward_demodulation,[],[f297,f187])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | (~spl7_7 | ~spl7_40)),
% 0.21/0.50    inference(superposition,[],[f121,f286])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ~spl7_17 | spl7_41 | ~spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f283,f140,f289,f160])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    u1_struct_0(sK2) = k2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~spl7_12),
% 0.21/0.50    inference(resolution,[],[f184,f141])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X1)) )),
% 0.21/0.50    inference(resolution,[],[f181,f77])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f74,f76])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ~spl7_17 | spl7_40 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f282,f132,f285,f160])).
% 0.21/0.50  % (8899)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    u1_struct_0(sK3) = k2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f184,f133])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ~spl7_17 | ~spl7_12 | spl7_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f280,f255,f140,f160])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | (~spl7_12 | spl7_35)),
% 0.21/0.50    inference(resolution,[],[f279,f141])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl7_35),
% 0.21/0.50    inference(resolution,[],[f256,f77])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ~l1_pre_topc(sK2) | spl7_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f255])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~spl7_34 | ~spl7_35 | spl7_39 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f264,f116,f276,f255,f252])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    spl7_34 <=> v2_pre_topc(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl7_6),
% 0.21/0.50    inference(superposition,[],[f87,f117])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~spl7_18 | ~spl7_17 | ~spl7_12 | spl7_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f273,f252,f140,f160,f164])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_12 | spl7_34)),
% 0.21/0.50    inference(resolution,[],[f261,f141])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl7_34),
% 0.21/0.50    inference(resolution,[],[f253,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ~v2_pre_topc(sK2) | spl7_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f252])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ~spl7_34 | ~spl7_35 | spl7_36 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f240,f116,f258,f255,f252])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    v1_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl7_6),
% 0.21/0.50    inference(superposition,[],[f86,f117])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl7_22 | ~spl7_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f182,f148,f186])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_14),
% 0.21/0.50    inference(resolution,[],[f181,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    l1_pre_topc(sK1) | ~spl7_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f148])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl7_20 | ~spl7_2 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f104,f100,f173])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl7_2 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl7_2 | ~spl7_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f101,f105])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~spl7_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f168])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f51,f50,f49,f48,f47,f46,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl7_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f164])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl7_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f160])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~spl7_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f156])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl7_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f152])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl7_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f148])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~spl7_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f144])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f140])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~spl7_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f136])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f132])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl7_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f128])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl7_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f124])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f120])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f68,f116])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl7_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f70,f108])).
% 0.21/0.50  % (8906)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f71,f104])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    sK5 = sK6),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl7_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f72,f100])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ~spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f96])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8901)------------------------------
% 0.21/0.50  % (8901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8901)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8901)Memory used [KB]: 11257
% 0.21/0.50  % (8901)Time elapsed: 0.029 s
% 0.21/0.50  % (8901)------------------------------
% 0.21/0.50  % (8901)------------------------------
% 0.21/0.50  % (8902)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (8891)Success in time 0.144 s
%------------------------------------------------------------------------------
