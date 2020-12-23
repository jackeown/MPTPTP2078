%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 590 expanded)
%              Number of leaves         :   35 ( 237 expanded)
%              Depth                    :   12
%              Number of atoms          :  704 (1833 expanded)
%              Number of equality atoms :   85 ( 295 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f752,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f88,f92,f96,f121,f128,f138,f142,f160,f175,f194,f295,f329,f342,f347,f404,f459,f464,f475,f488,f492,f541,f547,f612,f618,f733,f737,f751])).

fof(f751,plain,
    ( ~ spl3_11
    | ~ spl3_53
    | ~ spl3_61
    | ~ spl3_62
    | spl3_73 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_53
    | ~ spl3_61
    | ~ spl3_62
    | spl3_73 ),
    inference(subsumption_resolution,[],[f749,f736])).

fof(f736,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_73 ),
    inference(avatar_component_clause,[],[f735])).

fof(f735,plain,
    ( spl3_73
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f749,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | ~ spl3_53
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(resolution,[],[f647,f540])).

fof(f540,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl3_53
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f647,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_11
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f646,f141])).

fof(f141,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_11
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f646,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f636,f611])).

fof(f611,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl3_61
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f636,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_62 ),
    inference(resolution,[],[f617,f60])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X1,X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 != X0
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f617,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl3_62
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f737,plain,
    ( ~ spl3_73
    | spl3_8
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f249,f230,f123,f735])).

fof(f123,plain,
    ( spl3_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f230,plain,
    ( spl3_24
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f249,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_8
    | ~ spl3_24 ),
    inference(superposition,[],[f124,f231])).

fof(f231,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f230])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f733,plain,
    ( spl3_51
    | ~ spl3_11
    | ~ spl3_53
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f727,f616,f610,f539,f140,f490])).

fof(f490,plain,
    ( spl3_51
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f727,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ spl3_11
    | ~ spl3_53
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(resolution,[],[f645,f540])).

fof(f645,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl3_11
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f644,f141])).

fof(f644,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl3_61
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f635,f611])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl3_62 ),
    inference(resolution,[],[f617,f61])).

fof(f61,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 != X0
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f618,plain,
    ( spl3_62
    | ~ spl3_24
    | ~ spl3_32
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f478,f345,f286,f230,f616])).

fof(f286,plain,
    ( spl3_32
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f345,plain,
    ( spl3_41
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f478,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_24
    | ~ spl3_32
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f434,f287])).

fof(f287,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f286])).

fof(f434,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_24
    | ~ spl3_41 ),
    inference(superposition,[],[f346,f231])).

fof(f346,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f345])).

fof(f612,plain,
    ( spl3_61
    | ~ spl3_24
    | ~ spl3_32
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f480,f293,f286,f230,f610])).

fof(f293,plain,
    ( spl3_33
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f480,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_24
    | ~ spl3_32
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f432,f287])).

fof(f432,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl3_24
    | ~ spl3_33 ),
    inference(superposition,[],[f294,f231])).

fof(f294,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f293])).

fof(f547,plain,
    ( spl3_26
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f413,f286,f86,f237])).

fof(f237,plain,
    ( spl3_26
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f86,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f413,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f130,f287])).

fof(f130,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f120,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f120,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f541,plain,
    ( spl3_53
    | ~ spl3_16
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f521,f286,f173,f539])).

fof(f173,plain,
    ( spl3_16
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f521,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl3_16
    | ~ spl3_32 ),
    inference(superposition,[],[f174,f287])).

fof(f174,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f492,plain,
    ( ~ spl3_51
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f487,f338,f126,f94,f90,f83,f67,f63,f490])).

fof(f63,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( spl3_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( spl3_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f126,plain,
    ( spl3_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f338,plain,
    ( spl3_40
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f487,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f127,f412])).

fof(f412,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f133,f405])).

fof(f405,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f338])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f131,f113])).

fof(f113,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f112,f104])).

fof(f104,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f97,f95])).

fof(f95,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f112,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f76,f98])).

fof(f98,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f76,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f74,f64])).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f74,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f68,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f131,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f127,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f488,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f412,f338,f94,f90,f83,f67,f63,f230])).

fof(f475,plain,
    ( spl3_8
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_20
    | ~ spl3_33
    | spl3_40
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl3_8
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_20
    | ~ spl3_33
    | spl3_40
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f472,f124])).

fof(f472,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_20
    | ~ spl3_33
    | spl3_40
    | ~ spl3_41 ),
    inference(resolution,[],[f454,f174])).

fof(f454,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33
    | spl3_40
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f370,f343])).

fof(f343,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_20
    | spl3_40 ),
    inference(superposition,[],[f339,f193])).

fof(f193,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_20
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f339,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f338])).

fof(f370,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | k1_xboole_0 = k1_relat_1(sK2)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f369,f141])).

fof(f369,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_relat_1(sK2),X1)
        | k1_xboole_0 = k1_relat_1(sK2)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f361,f294])).

fof(f361,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_relat_1(sK2),X1)
        | k1_xboole_0 = k1_relat_1(sK2)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl3_41 ),
    inference(resolution,[],[f346,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f464,plain,
    ( spl3_9
    | ~ spl3_11
    | ~ spl3_16
    | spl3_32
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f394,f345,f293,f286,f173,f140,f126])).

fof(f394,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_11
    | ~ spl3_16
    | spl3_32
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(resolution,[],[f368,f174])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl3_11
    | spl3_32
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f367,f331])).

fof(f331,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f286])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k1_relat_1(sK2)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f366,f141])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k1_relat_1(sK2)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f360,f294])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k1_relat_1(sK2)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl3_41 ),
    inference(resolution,[],[f346,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f459,plain,
    ( ~ spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_40 ),
    inference(avatar_split_clause,[],[f456,f338,f94,f90,f83,f67,f63,f230])).

fof(f456,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_40 ),
    inference(subsumption_resolution,[],[f134,f339])).

fof(f134,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f132,f113])).

fof(f132,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(resolution,[],[f84,f45])).

fof(f404,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f347,plain,
    ( spl3_41
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f154,f140,f94,f90,f83,f67,f63,f345])).

fof(f154,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f153,f113])).

fof(f153,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f152,f111])).

fof(f111,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f77,f98])).

fof(f77,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f75,f64])).

fof(f75,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f152,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f146,f84])).

fof(f146,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_11 ),
    inference(resolution,[],[f141,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f342,plain,
    ( ~ spl3_24
    | ~ spl3_12
    | spl3_26 ),
    inference(avatar_split_clause,[],[f333,f237,f158,f230])).

fof(f158,plain,
    ( spl3_12
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f333,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_12
    | spl3_26 ),
    inference(superposition,[],[f328,f159])).

fof(f159,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f328,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f237])).

fof(f329,plain,
    ( spl3_32
    | ~ spl3_26
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f129,f86,f237,f286])).

fof(f129,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f120,f44])).

fof(f295,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f151,f140,f94,f90,f83,f67,f63,f293])).

fof(f151,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f150,f113])).

fof(f150,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f149,f111])).

fof(f149,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f145,f84])).

fof(f145,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_11 ),
    inference(resolution,[],[f141,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f194,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f111,f90,f67,f63,f192])).

fof(f175,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f144,f136,f86,f173])).

fof(f136,plain,
    ( spl3_10
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f144,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f143,f120])).

fof(f143,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(resolution,[],[f137,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f137,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f160,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f104,f94,f90,f158])).

fof(f142,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f114,f90,f63,f140])).

fof(f114,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f73,f98])).

fof(f73,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f138,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f90,f136])).

fof(f103,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f128,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f115,f90,f63,f126,f123])).

fof(f115,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f34,f114])).

fof(f34,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f121,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f98,f90,f86])).

fof(f96,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f39,f94])).

fof(f39,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f72,f63,f86,f83])).

fof(f72,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:48:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (6912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (6927)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (6930)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (6919)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (6912)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (6913)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (6917)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f752,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f65,f69,f88,f92,f96,f121,f128,f138,f142,f160,f175,f194,f295,f329,f342,f347,f404,f459,f464,f475,f488,f492,f541,f547,f612,f618,f733,f737,f751])).
% 0.21/0.53  fof(f751,plain,(
% 0.21/0.53    ~spl3_11 | ~spl3_53 | ~spl3_61 | ~spl3_62 | spl3_73),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f750])).
% 0.21/0.53  fof(f750,plain,(
% 0.21/0.53    $false | (~spl3_11 | ~spl3_53 | ~spl3_61 | ~spl3_62 | spl3_73)),
% 0.21/0.53    inference(subsumption_resolution,[],[f749,f736])).
% 0.21/0.53  fof(f736,plain,(
% 0.21/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_73),
% 0.21/0.53    inference(avatar_component_clause,[],[f735])).
% 0.21/0.53  fof(f735,plain,(
% 0.21/0.53    spl3_73 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.53  fof(f749,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | ~spl3_53 | ~spl3_61 | ~spl3_62)),
% 0.21/0.53    inference(resolution,[],[f647,f540])).
% 0.21/0.53  fof(f540,plain,(
% 0.21/0.53    r1_tarski(k1_xboole_0,sK0) | ~spl3_53),
% 0.21/0.53    inference(avatar_component_clause,[],[f539])).
% 0.21/0.53  fof(f539,plain,(
% 0.21/0.53    spl3_53 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.53  fof(f647,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_11 | ~spl3_61 | ~spl3_62)),
% 0.21/0.53    inference(subsumption_resolution,[],[f646,f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    spl3_11 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f646,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_61 | ~spl3_62)),
% 0.21/0.53    inference(subsumption_resolution,[],[f636,f611])).
% 0.21/0.53  fof(f611,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~spl3_61),
% 0.21/0.53    inference(avatar_component_clause,[],[f610])).
% 0.21/0.53  fof(f610,plain,(
% 0.21/0.53    spl3_61 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.53  fof(f636,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl3_62),
% 0.21/0.53    inference(resolution,[],[f617,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3) | ~r1_tarski(X1,X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 != X0 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.53  fof(f617,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_62),
% 0.21/0.53    inference(avatar_component_clause,[],[f616])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    spl3_62 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.53  fof(f737,plain,(
% 0.21/0.53    ~spl3_73 | spl3_8 | ~spl3_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f249,f230,f123,f735])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl3_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    spl3_24 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_8 | ~spl3_24)),
% 0.21/0.53    inference(superposition,[],[f124,f231])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl3_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f230])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f123])).
% 0.21/0.53  fof(f733,plain,(
% 0.21/0.53    spl3_51 | ~spl3_11 | ~spl3_53 | ~spl3_61 | ~spl3_62),
% 0.21/0.53    inference(avatar_split_clause,[],[f727,f616,f610,f539,f140,f490])).
% 0.21/0.53  fof(f490,plain,(
% 0.21/0.53    spl3_51 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.53  fof(f727,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (~spl3_11 | ~spl3_53 | ~spl3_61 | ~spl3_62)),
% 0.21/0.53    inference(resolution,[],[f645,f540])).
% 0.21/0.53  fof(f645,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | (~spl3_11 | ~spl3_61 | ~spl3_62)),
% 0.21/0.53    inference(subsumption_resolution,[],[f644,f141])).
% 0.21/0.53  fof(f644,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | (~spl3_61 | ~spl3_62)),
% 0.21/0.53    inference(subsumption_resolution,[],[f635,f611])).
% 0.21/0.53  fof(f635,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | ~spl3_62),
% 0.21/0.53    inference(resolution,[],[f617,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3) | ~r1_tarski(X1,X2) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 != X0 | v1_funct_2(X3,X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f618,plain,(
% 0.21/0.53    spl3_62 | ~spl3_24 | ~spl3_32 | ~spl3_41),
% 0.21/0.53    inference(avatar_split_clause,[],[f478,f345,f286,f230,f616])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    spl3_32 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    spl3_41 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.53  fof(f478,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_24 | ~spl3_32 | ~spl3_41)),
% 0.21/0.53    inference(forward_demodulation,[],[f434,f287])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f286])).
% 0.21/0.53  fof(f434,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl3_24 | ~spl3_41)),
% 0.21/0.53    inference(superposition,[],[f346,f231])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_41),
% 0.21/0.53    inference(avatar_component_clause,[],[f345])).
% 0.21/0.53  fof(f612,plain,(
% 0.21/0.53    spl3_61 | ~spl3_24 | ~spl3_32 | ~spl3_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f480,f293,f286,f230,f610])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    spl3_33 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.53  fof(f480,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl3_24 | ~spl3_32 | ~spl3_33)),
% 0.21/0.53    inference(forward_demodulation,[],[f432,f287])).
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | (~spl3_24 | ~spl3_33)),
% 0.21/0.53    inference(superposition,[],[f294,f231])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl3_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f293])).
% 0.21/0.53  fof(f547,plain,(
% 0.21/0.53    spl3_26 | ~spl3_5 | ~spl3_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f413,f286,f86,f237])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    spl3_26 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK2) | (~spl3_5 | ~spl3_32)),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f287])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~spl3_5),
% 0.21/0.53    inference(resolution,[],[f120,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    spl3_53 | ~spl3_16 | ~spl3_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f521,f286,f173,f539])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl3_16 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f521,plain,(
% 0.21/0.53    r1_tarski(k1_xboole_0,sK0) | (~spl3_16 | ~spl3_32)),
% 0.21/0.53    inference(superposition,[],[f174,f287])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f173])).
% 0.21/0.53  fof(f492,plain,(
% 0.21/0.53    ~spl3_51 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9 | ~spl3_40),
% 0.21/0.53    inference(avatar_split_clause,[],[f487,f338,f126,f94,f90,f83,f67,f63,f490])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl3_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl3_7 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl3_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    spl3_40 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.53  fof(f487,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9 | ~spl3_40)),
% 0.21/0.53    inference(forward_demodulation,[],[f127,f412])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_40)),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f405])).
% 0.21/0.53  fof(f405,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | ~spl3_40),
% 0.21/0.53    inference(avatar_component_clause,[],[f338])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f131,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f112,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    sK1 = k2_relat_1(sK2) | (~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f97,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_6),
% 0.21/0.53    inference(resolution,[],[f91,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.53    inference(resolution,[],[f91,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f68,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f84,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f126])).
% 0.21/0.53  fof(f488,plain,(
% 0.21/0.53    spl3_24 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_40),
% 0.21/0.53    inference(avatar_split_clause,[],[f412,f338,f94,f90,f83,f67,f63,f230])).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    spl3_8 | ~spl3_11 | ~spl3_16 | ~spl3_20 | ~spl3_33 | spl3_40 | ~spl3_41),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f474])).
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    $false | (spl3_8 | ~spl3_11 | ~spl3_16 | ~spl3_20 | ~spl3_33 | spl3_40 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f472,f124])).
% 0.21/0.53  fof(f472,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_11 | ~spl3_16 | ~spl3_20 | ~spl3_33 | spl3_40 | ~spl3_41)),
% 0.21/0.53    inference(resolution,[],[f454,f174])).
% 0.21/0.53  fof(f454,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl3_11 | ~spl3_20 | ~spl3_33 | spl3_40 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f370,f343])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_20 | spl3_40)),
% 0.21/0.53    inference(superposition,[],[f339,f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f192])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    spl3_20 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | spl3_40),
% 0.21/0.53    inference(avatar_component_clause,[],[f338])).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl3_11 | ~spl3_33 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f369,f141])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl3_33 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f361,f294])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | ~spl3_41),
% 0.21/0.53    inference(resolution,[],[f346,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f464,plain,(
% 0.21/0.53    spl3_9 | ~spl3_11 | ~spl3_16 | spl3_32 | ~spl3_33 | ~spl3_41),
% 0.21/0.53    inference(avatar_split_clause,[],[f394,f345,f293,f286,f173,f140,f126])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_11 | ~spl3_16 | spl3_32 | ~spl3_33 | ~spl3_41)),
% 0.21/0.53    inference(resolution,[],[f368,f174])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | (~spl3_11 | spl3_32 | ~spl3_33 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f367,f331])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relat_1(sK2) | spl3_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f286])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | (~spl3_11 | ~spl3_33 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f366,f141])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | (~spl3_33 | ~spl3_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f360,f294])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | ~spl3_41),
% 0.21/0.53    inference(resolution,[],[f346,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f459,plain,(
% 0.21/0.53    ~spl3_24 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_40),
% 0.21/0.53    inference(avatar_split_clause,[],[f456,f338,f94,f90,f83,f67,f63,f230])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_40)),
% 0.21/0.53    inference(subsumption_resolution,[],[f134,f339])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f132,f113])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != k1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f84,f45])).
% 0.21/0.53  fof(f404,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(sK2) | sK1 != k2_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    spl3_41 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f154,f140,f94,f90,f83,f67,f63,f345])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f153,f113])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f152,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f77,f98])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f64])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f68,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_4 | ~spl3_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f84])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_11),
% 0.21/0.53    inference(resolution,[],[f141,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    ~spl3_24 | ~spl3_12 | spl3_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f333,f237,f158,f230])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    spl3_12 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | (~spl3_12 | spl3_26)),
% 0.21/0.53    inference(superposition,[],[f328,f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    sK1 = k2_relat_1(sK2) | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f158])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(sK2) | spl3_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f237])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    spl3_32 | ~spl3_26 | ~spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f129,f86,f237,f286])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl3_5),
% 0.21/0.53    inference(resolution,[],[f120,f44])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    spl3_33 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f151,f140,f94,f90,f83,f67,f63,f293])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f150,f113])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f149,f111])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f84])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_11),
% 0.21/0.53    inference(resolution,[],[f141,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    spl3_20 | ~spl3_1 | ~spl3_2 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f111,f90,f67,f63,f192])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    spl3_16 | ~spl3_5 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f144,f136,f86,f173])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl3_10 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_5 | ~spl3_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f120])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl3_10),
% 0.21/0.53    inference(resolution,[],[f137,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    v4_relat_1(sK2,sK0) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl3_12 | ~spl3_6 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f104,f94,f90,f158])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl3_11 | ~spl3_1 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f114,f90,f63,f140])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f73,f98])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f64,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl3_10 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f103,f90,f136])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    v4_relat_1(sK2,sK0) | ~spl3_6),
% 0.21/0.53    inference(resolution,[],[f91,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~spl3_8 | ~spl3_9 | ~spl3_1 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f115,f90,f63,f126,f123])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_1 | ~spl3_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f34,f114])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl3_5 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f98,f90,f86])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f94])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f90])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl3_4 | ~spl3_5 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f72,f63,f86,f83])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f64,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f67])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v2_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f63])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (6912)------------------------------
% 0.21/0.53  % (6912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6912)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (6912)Memory used [KB]: 6524
% 0.21/0.53  % (6912)Time elapsed: 0.096 s
% 0.21/0.53  % (6912)------------------------------
% 0.21/0.53  % (6912)------------------------------
% 0.21/0.53  % (6911)Success in time 0.173 s
%------------------------------------------------------------------------------
