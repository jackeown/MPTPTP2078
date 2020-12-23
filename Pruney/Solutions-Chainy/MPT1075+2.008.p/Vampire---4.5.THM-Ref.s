%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 356 expanded)
%              Number of leaves         :   38 ( 150 expanded)
%              Depth                    :   12
%              Number of atoms          :  707 (1420 expanded)
%              Number of equality atoms :   75 ( 128 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f85,f89,f93,f139,f143,f159,f167,f176,f184,f185,f199,f204,f210,f228,f250,f267,f336,f384,f415,f416])).

fof(f416,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f415,plain,
    ( spl6_49
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f411,f382,f334,f265,f208,f73,f65,f413])).

fof(f413,plain,
    ( spl6_49
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f65,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f73,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f208,plain,
    ( spl6_26
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f265,plain,
    ( spl6_34
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f334,plain,
    ( spl6_41
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f382,plain,
    ( spl6_46
  <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f411,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f410,f383])).

fof(f383,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f382])).

fof(f410,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_34
    | ~ spl6_41 ),
    inference(resolution,[],[f349,f74])).

fof(f74,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_26
    | ~ spl6_34
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f348,f66])).

fof(f66,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f348,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_26
    | ~ spl6_34
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f347,f266])).

fof(f266,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f265])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_26
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f337,f209])).

fof(f209,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f208])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_41 ),
    inference(resolution,[],[f335,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f335,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f334])).

fof(f384,plain,
    ( spl6_46
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f364,f226,f197,f182,f178,f91,f87,f83,f69,f61,f57,f382])).

fof(f57,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f61,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f69,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f83,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f87,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f91,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f178,plain,
    ( spl6_20
  <=> sK0 = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f182,plain,
    ( spl6_21
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f197,plain,
    ( spl6_24
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f226,plain,
    ( spl6_30
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f364,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f363,f58])).

fof(f58,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f363,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f362,f88])).

fof(f88,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f362,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f361,f183])).

fof(f183,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f361,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(superposition,[],[f257,f179])).

fof(f179,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f256,f84])).

fof(f84,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_9
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f255,f92])).

fof(f92,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f254,f70])).

fof(f70,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f251,f62])).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(superposition,[],[f227,f198])).

fof(f198,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f227,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f336,plain,
    ( spl6_41
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f221,f91,f87,f83,f61,f57,f334])).

fof(f221,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f220,f58])).

fof(f220,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f130,f88])).

fof(f130,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ v1_funct_1(X5)
        | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f129,f62])).

fof(f129,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f115,f84])).

fof(f115,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f267,plain,
    ( spl6_34
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f219,f91,f87,f83,f61,f57,f265])).

fof(f219,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f218,f58])).

fof(f218,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f128,f88])).

fof(f128,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
        | ~ v1_funct_1(X3)
        | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f127,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
        | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f114,f84])).

fof(f114,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
        | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4) )
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f250,plain,
    ( spl6_3
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl6_3
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f238,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f238,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_29 ),
    inference(superposition,[],[f66,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_29
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f228,plain,
    ( spl6_29
    | spl6_30
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f80,f73,f226,f223])).

fof(f80,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(X1)
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f74,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f210,plain,
    ( spl6_26
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f206,f91,f87,f83,f61,f57,f208])).

fof(f206,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f205,f58])).

fof(f205,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f126,f88])).

fof(f126,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f125,f62])).

fof(f125,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1)) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f113,f84])).

fof(f113,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1)) )
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f21])).

% (30755)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (30752)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (30757)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (30760)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (30765)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (30769)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (30764)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (30756)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f204,plain,
    ( spl6_25
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f200,f91,f83,f73,f65,f61,f202])).

fof(f202,plain,
    ( spl6_25
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f200,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f124,f74])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f123,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f122,f84])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f112,f62])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f39])).

fof(f199,plain,
    ( spl6_24
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f117,f91,f197])).

fof(f117,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f185,plain,
    ( spl6_20
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f180,f174,f165,f178])).

fof(f165,plain,
    ( spl6_17
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f174,plain,
    ( spl6_19
  <=> k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f180,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f175,f166])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f175,plain,
    ( k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f184,plain,
    ( spl6_21
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f163,f157,f141,f182])).

fof(f141,plain,
    ( spl6_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f157,plain,
    ( spl6_16
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f163,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f162,f142])).

fof(f142,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f162,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f158,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f158,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f176,plain,
    ( spl6_19
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f98,f87,f174])).

fof(f98,plain,
    ( k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f167,plain,
    ( spl6_17
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f111,f87,f77,f165])).

fof(f77,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f111,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f109,f110])).

fof(f110,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f109,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f81,f100])).

fof(f100,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f88,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f81,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f78,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f78,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f159,plain,
    ( spl6_16
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f119,f91,f157])).

fof(f119,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f143,plain,
    ( spl6_12
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f131,f91,f141])).

fof(f131,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f120,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f46])).

fof(f139,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f31,f137])).

fof(f137,plain,
    ( spl6_11
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f31,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

% (30761)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(f93,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (30766)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (30750)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (30758)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (30750)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f85,f89,f93,f139,f143,f159,f167,f176,f184,f185,f199,f204,f210,f228,f250,f267,f336,f384,f415,f416])).
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    spl6_49 | spl6_3 | ~spl6_5 | ~spl6_26 | ~spl6_34 | ~spl6_41 | ~spl6_46),
% 0.21/0.48    inference(avatar_split_clause,[],[f411,f382,f334,f265,f208,f73,f65,f413])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    spl6_49 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl6_3 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    spl6_26 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl6_34 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    spl6_41 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    spl6_46 <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_26 | ~spl6_34 | ~spl6_41 | ~spl6_46)),
% 0.21/0.48    inference(forward_demodulation,[],[f410,f383])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_46),
% 0.21/0.48    inference(avatar_component_clause,[],[f382])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_3 | ~spl6_5 | ~spl6_26 | ~spl6_34 | ~spl6_41)),
% 0.21/0.48    inference(resolution,[],[f349,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_26 | ~spl6_34 | ~spl6_41)),
% 0.21/0.48    inference(subsumption_resolution,[],[f348,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_26 | ~spl6_34 | ~spl6_41)),
% 0.21/0.48    inference(subsumption_resolution,[],[f347,f266])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~spl6_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f265])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_26 | ~spl6_41)),
% 0.21/0.48    inference(subsumption_resolution,[],[f337,f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~spl6_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f208])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | ~spl6_41),
% 0.21/0.48    inference(resolution,[],[f335,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_41),
% 0.21/0.48    inference(avatar_component_clause,[],[f334])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    spl6_46 | ~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_20 | ~spl6_21 | ~spl6_24 | ~spl6_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f364,f226,f197,f182,f178,f91,f87,f83,f69,f61,f57,f382])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl6_1 <=> v1_funct_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl6_4 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl6_20 <=> sK0 = k1_relset_1(sK0,sK2,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl6_21 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl6_24 <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    spl6_30 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_20 | ~spl6_21 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f363,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    v1_funct_1(sK4) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_20 | ~spl6_21 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f362,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_20 | ~spl6_21 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f361,f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f182])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),sK0) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_20 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(superposition,[],[f257,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK2,sK4) | ~spl6_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f178])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1)) ) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f256,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | spl6_4 | ~spl6_9 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | spl6_4 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f254,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | v1_xboole_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | ~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f251,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_24 | ~spl6_30)),
% 0.21/0.48    inference(superposition,[],[f227,f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) | ~v1_funct_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl6_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f226])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    spl6_41 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f221,f91,f87,f83,f61,f57,f334])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f220,f58])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.48    inference(resolution,[],[f130,f88])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~v1_funct_1(X5) | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f62])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X6,X5] : (~v1_funct_1(sK3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | (~spl6_7 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f84])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X6,X5] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f92,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    spl6_34 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f219,f91,f87,f83,f61,f57,f265])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f218,f58])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.48    inference(resolution,[],[f128,f88])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~v1_funct_1(X3) | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f62])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~v1_funct_1(sK3) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4)) ) | (~spl6_7 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f84])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4)) ) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f92,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    spl6_3 | ~spl6_29),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f249])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    $false | (spl6_3 | ~spl6_29)),
% 0.21/0.48    inference(subsumption_resolution,[],[f238,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_29)),
% 0.21/0.48    inference(superposition,[],[f66,f224])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl6_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl6_29 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    spl6_29 | spl6_30 | ~spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f73,f226,f223])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) ) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f74,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    spl6_26 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f206,f91,f87,f83,f61,f57,f208])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f58])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.48    inference(resolution,[],[f126,f88])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~v1_funct_1(X1) | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f62])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1))) ) | (~spl6_7 | ~spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f84])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1))) ) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f92,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % (30755)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (30752)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (30757)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (30760)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (30765)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (30769)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (30764)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (30756)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl6_25 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f91,f83,f73,f65,f61,f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl6_25 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(resolution,[],[f124,f74])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f66])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f84])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f62])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f92,f39])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl6_24 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f117,f91,f197])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f92,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl6_20 | ~spl6_17 | ~spl6_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f180,f174,f165,f178])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl6_17 <=> sK0 = k1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    spl6_19 <=> k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK2,sK4) | (~spl6_17 | ~spl6_19)),
% 0.21/0.50    inference(forward_demodulation,[],[f175,f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK4) | ~spl6_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) | ~spl6_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f174])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl6_21 | ~spl6_12 | ~spl6_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f157,f141,f182])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl6_12 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl6_16 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK3),sK0) | (~spl6_12 | ~spl6_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | ~spl6_16),
% 0.21/0.50    inference(resolution,[],[f158,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    v5_relat_1(sK3,sK0) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f157])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl6_19 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f98,f87,f174])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) | ~spl6_8),
% 0.21/0.50    inference(resolution,[],[f88,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl6_17 | ~spl6_6 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f111,f87,f77,f165])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK4) | (~spl6_6 | ~spl6_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f109,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v1_relat_1(sK4) | ~spl6_8),
% 0.21/0.50    inference(subsumption_resolution,[],[f102,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK4) | ~spl6_8),
% 0.21/0.50    inference(resolution,[],[f88,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl6_6 | ~spl6_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v4_relat_1(sK4,sK0) | ~spl6_8),
% 0.21/0.50    inference(resolution,[],[f88,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~v4_relat_1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_6),
% 0.21/0.50    inference(resolution,[],[f78,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl6_16 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f119,f91,f157])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    v5_relat_1(sK3,sK0) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f92,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl6_12 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f131,f91,f141])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl6_9),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f47])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f92,f46])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~spl6_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl6_11 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  % (30761)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f91])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f87])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f83])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f77])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v1_partfun1(sK4,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f73])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    m1_subset_1(sK5,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f69])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f65])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f61])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f57])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30750)------------------------------
% 0.21/0.50  % (30750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30750)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30750)Memory used [KB]: 6524
% 0.21/0.50  % (30750)Time elapsed: 0.070 s
% 0.21/0.50  % (30750)------------------------------
% 0.21/0.50  % (30750)------------------------------
% 0.21/0.50  % (30770)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (30749)Success in time 0.146 s
%------------------------------------------------------------------------------
