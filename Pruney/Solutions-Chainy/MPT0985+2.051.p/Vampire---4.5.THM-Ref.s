%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 725 expanded)
%              Number of leaves         :   41 ( 252 expanded)
%              Depth                    :   15
%              Number of atoms          :  658 (3399 expanded)
%              Number of equality atoms :   95 ( 564 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1809,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f171,f179,f184,f194,f228,f230,f473,f579,f734,f735,f895,f897,f899,f900,f973,f1104,f1200,f1210,f1214,f1220,f1228,f1288,f1386,f1423,f1526,f1531,f1711,f1808])).

fof(f1808,plain,
    ( spl4_2
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_58
    | ~ spl4_71
    | ~ spl4_119 ),
    inference(avatar_contradiction_clause,[],[f1804])).

fof(f1804,plain,
    ( $false
    | spl4_2
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_58
    | ~ spl4_71
    | ~ spl4_119 ),
    inference(subsumption_resolution,[],[f1501,f1797])).

fof(f1797,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_71
    | ~ spl4_119 ),
    inference(resolution,[],[f1710,f1495])).

fof(f1495,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_71 ),
    inference(backward_demodulation,[],[f1365,f940])).

fof(f940,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl4_71
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1365,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f1236,f356])).

fof(f356,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl4_29
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1236,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f159,f210])).

fof(f210,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f159,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1710,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_119 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f1709,plain,
    ( spl4_119
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f1501,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_58
    | ~ spl4_71 ),
    inference(backward_demodulation,[],[f767,f1493])).

fof(f1493,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(backward_demodulation,[],[f1398,f940])).

fof(f1398,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40 ),
    inference(backward_demodulation,[],[f459,f1367])).

fof(f1367,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f1242,f356])).

fof(f1242,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f337,f210])).

fof(f337,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f196,f87])).

fof(f87,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f73])).

fof(f73,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f196,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f85,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

fof(f459,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl4_40
  <=> k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f767,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f766])).

fof(f766,plain,
    ( spl4_58
  <=> r1_tarski(k1_relat_1(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f1711,plain,
    ( ~ spl4_39
    | ~ spl4_117
    | spl4_119
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f1696,f1529,f1709,f1524,f455])).

fof(f455,plain,
    ( spl4_39
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1524,plain,
    ( spl4_117
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f1529,plain,
    ( spl4_118
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f1696,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl4_118 ),
    inference(resolution,[],[f1530,f152])).

fof(f152,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f71,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f1530,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f1529])).

fof(f1531,plain,
    ( ~ spl4_37
    | ~ spl4_39
    | spl4_118
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(avatar_split_clause,[],[f1527,f939,f458,f355,f209,f1529,f455,f445])).

fof(f445,plain,
    ( spl4_37
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1527,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(forward_demodulation,[],[f1506,f1367])).

fof(f1506,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(superposition,[],[f108,f1493])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1526,plain,
    ( ~ spl4_37
    | ~ spl4_39
    | spl4_117
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(avatar_split_clause,[],[f1522,f939,f458,f355,f209,f1524,f455,f445])).

fof(f1522,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(forward_demodulation,[],[f1505,f1367])).

fof(f1505,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_40
    | ~ spl4_71 ),
    inference(superposition,[],[f107,f1493])).

fof(f107,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1423,plain,
    ( ~ spl4_37
    | spl4_76
    | ~ spl4_11
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f1405,f355,f209,f969,f445])).

fof(f969,plain,
    ( spl4_76
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f1405,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29 ),
    inference(trivial_inequality_removal,[],[f1403])).

fof(f1403,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_29 ),
    inference(superposition,[],[f105,f1367])).

fof(f105,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f1386,plain,
    ( ~ spl4_37
    | spl4_58
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f1385,f355,f766,f445])).

fof(f1385,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_29 ),
    inference(resolution,[],[f1345,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1345,plain,
    ( v4_relat_1(k1_xboole_0,sK0)
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f197,f356])).

fof(f197,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f85,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1288,plain,
    ( ~ spl4_37
    | spl4_38
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f1287,f455,f448,f445])).

fof(f448,plain,
    ( spl4_38
  <=> v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1287,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_39 ),
    inference(resolution,[],[f578,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f578,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f455])).

fof(f1228,plain,
    ( spl4_29
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f1227,f209,f355])).

fof(f1227,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f195,f807])).

fof(f807,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f103,f337])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f195,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f85,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1220,plain,
    ( ~ spl4_32
    | ~ spl4_96 ),
    inference(avatar_contradiction_clause,[],[f1216])).

fof(f1216,plain,
    ( $false
    | ~ spl4_32
    | ~ spl4_96 ),
    inference(subsumption_resolution,[],[f376,f1206])).

fof(f1206,plain,
    ( ! [X0] : ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1205,plain,
    ( spl4_96
  <=> ! [X0] : ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f376,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl4_32
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1214,plain,(
    spl4_97 ),
    inference(avatar_contradiction_clause,[],[f1212])).

fof(f1212,plain,
    ( $false
    | spl4_97 ),
    inference(subsumption_resolution,[],[f1209,f237])).

fof(f237,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(global_subsumption,[],[f195,f236])).

fof(f236,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f197,f118])).

fof(f1209,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_97 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f1208,plain,
    ( spl4_97
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f1210,plain,
    ( spl4_96
    | ~ spl4_97
    | spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f1203,f182,f161,f1208,f1205])).

fof(f161,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f182,plain,
    ( spl4_7
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1203,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1201,f183])).

fof(f183,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1201,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl4_3 ),
    inference(resolution,[],[f162,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f162,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1200,plain,
    ( spl4_2
    | ~ spl4_87 ),
    inference(avatar_contradiction_clause,[],[f1198])).

fof(f1198,plain,
    ( $false
    | spl4_2
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f237,f1197])).

fof(f1197,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_2
    | ~ spl4_87 ),
    inference(resolution,[],[f1103,f159])).

fof(f1103,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f1102,plain,
    ( spl4_87
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f1104,plain,
    ( ~ spl4_1
    | ~ spl4_31
    | spl4_87
    | spl4_28
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f1095,f375,f332,f1102,f370,f155])).

% (9800)Refutation not found, incomplete strategy% (9800)------------------------------
% (9800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9800)Termination reason: Refutation not found, incomplete strategy

% (9800)Memory used [KB]: 6652
% (9800)Time elapsed: 0.173 s
% (9800)------------------------------
% (9800)------------------------------
fof(f155,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f370,plain,
    ( spl4_31
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f332,plain,
    ( spl4_28
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1095,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl4_32 ),
    inference(resolution,[],[f376,f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f973,plain,
    ( ~ spl4_38
    | spl4_71
    | ~ spl4_76
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f948,f462,f969,f939,f448])).

fof(f462,plain,
    ( spl4_41
  <=> k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f948,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_41 ),
    inference(superposition,[],[f103,f463])).

fof(f463,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f462])).

fof(f900,plain,
    ( ~ spl4_5
    | spl4_23
    | ~ spl4_28
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f891,f182,f332,f303,f169])).

fof(f169,plain,
    ( spl4_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f303,plain,
    ( spl4_23
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f891,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(superposition,[],[f103,f183])).

fof(f899,plain,
    ( ~ spl4_5
    | ~ spl4_28
    | spl4_11
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f898,f182,f177,f209,f332,f169])).

fof(f177,plain,
    ( spl4_6
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f898,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f890,f338])).

fof(f338,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f178,f337])).

fof(f178,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f890,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(superposition,[],[f105,f183])).

fof(f897,plain,
    ( ~ spl4_5
    | ~ spl4_1
    | spl4_32
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f896,f182,f177,f375,f155,f169])).

fof(f896,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f889,f338])).

fof(f889,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(superposition,[],[f108,f183])).

fof(f895,plain,
    ( ~ spl4_5
    | ~ spl4_1
    | spl4_31
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f894,f182,f177,f370,f155,f169])).

fof(f894,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f888,f338])).

fof(f888,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(superposition,[],[f107,f183])).

fof(f735,plain,
    ( ~ spl4_37
    | ~ spl4_39
    | spl4_41
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f732,f355,f462,f455,f445])).

fof(f732,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_29 ),
    inference(resolution,[],[f722,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f722,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f86,f356])).

fof(f86,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f734,plain,
    ( ~ spl4_37
    | ~ spl4_39
    | spl4_40
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f731,f355,f458,f455,f445])).

fof(f731,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_29 ),
    inference(resolution,[],[f722,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f579,plain,
    ( ~ spl4_4
    | ~ spl4_9
    | spl4_39
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f577,f303,f455,f192,f166])).

fof(f166,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f192,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f577,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f110,f304])).

fof(f304,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f303])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f473,plain,
    ( ~ spl4_29
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl4_29
    | spl4_37 ),
    inference(subsumption_resolution,[],[f435,f446])).

fof(f446,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f445])).

fof(f435,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f195,f356])).

fof(f230,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f83,f193])).

fof(f193,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f192])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f228,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f167,f195])).

fof(f167,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f166])).

fof(f194,plain,
    ( ~ spl4_4
    | ~ spl4_9
    | spl4_1 ),
    inference(avatar_split_clause,[],[f190,f155,f192,f166])).

fof(f190,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f156,f110])).

fof(f156,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f184,plain,
    ( ~ spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f180,f182,f166])).

fof(f180,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f83,f173])).

fof(f173,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f86,f113])).

fof(f179,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f175,f177,f166])).

fof(f175,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f83,f172])).

fof(f172,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f86,f112])).

fof(f171,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f164,f169,f166])).

fof(f164,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f109])).

fof(f163,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f88,f161,f158,f155])).

fof(f88,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (9805)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (9798)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (9797)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (9800)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (9799)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (9806)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (9815)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (9796)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (9809)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (9810)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (9808)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9807)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (9821)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (9819)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (9801)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (9820)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (9811)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (9802)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (9822)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (9823)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (9813)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (9816)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (9812)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (9818)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (9813)Refutation not found, incomplete strategy% (9813)------------------------------
% 0.22/0.54  % (9813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9813)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9813)Memory used [KB]: 10746
% 0.22/0.54  % (9813)Time elapsed: 0.120 s
% 0.22/0.54  % (9813)------------------------------
% 0.22/0.54  % (9813)------------------------------
% 0.22/0.54  % (9824)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (9825)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (9803)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (9817)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (9814)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (9804)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (9818)Refutation not found, incomplete strategy% (9818)------------------------------
% 0.22/0.57  % (9818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9798)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.59  % (9818)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (9818)Memory used [KB]: 11129
% 0.22/0.59  % (9818)Time elapsed: 0.134 s
% 0.22/0.59  % (9818)------------------------------
% 0.22/0.59  % (9818)------------------------------
% 1.74/0.60  % SZS output start Proof for theBenchmark
% 1.74/0.60  fof(f1809,plain,(
% 1.74/0.60    $false),
% 1.74/0.60    inference(avatar_sat_refutation,[],[f163,f171,f179,f184,f194,f228,f230,f473,f579,f734,f735,f895,f897,f899,f900,f973,f1104,f1200,f1210,f1214,f1220,f1228,f1288,f1386,f1423,f1526,f1531,f1711,f1808])).
% 1.74/0.60  fof(f1808,plain,(
% 1.74/0.60    spl4_2 | ~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_58 | ~spl4_71 | ~spl4_119),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1804])).
% 1.74/0.60  fof(f1804,plain,(
% 1.74/0.60    $false | (spl4_2 | ~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_58 | ~spl4_71 | ~spl4_119)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1501,f1797])).
% 1.74/0.60  fof(f1797,plain,(
% 1.74/0.60    ~r1_tarski(k1_xboole_0,sK0) | (spl4_2 | ~spl4_11 | ~spl4_29 | ~spl4_71 | ~spl4_119)),
% 1.74/0.60    inference(resolution,[],[f1710,f1495])).
% 1.74/0.60  fof(f1495,plain,(
% 1.74/0.60    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl4_2 | ~spl4_11 | ~spl4_29 | ~spl4_71)),
% 1.74/0.60    inference(backward_demodulation,[],[f1365,f940])).
% 1.74/0.60  fof(f940,plain,(
% 1.74/0.60    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl4_71),
% 1.74/0.60    inference(avatar_component_clause,[],[f939])).
% 1.74/0.60  fof(f939,plain,(
% 1.74/0.60    spl4_71 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.74/0.60  fof(f1365,plain,(
% 1.74/0.60    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_11 | ~spl4_29)),
% 1.74/0.60    inference(backward_demodulation,[],[f1236,f356])).
% 1.74/0.60  fof(f356,plain,(
% 1.74/0.60    k1_xboole_0 = sK2 | ~spl4_29),
% 1.74/0.60    inference(avatar_component_clause,[],[f355])).
% 1.74/0.60  fof(f355,plain,(
% 1.74/0.60    spl4_29 <=> k1_xboole_0 = sK2),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.74/0.60  fof(f1236,plain,(
% 1.74/0.60    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_11)),
% 1.74/0.60    inference(backward_demodulation,[],[f159,f210])).
% 1.74/0.60  fof(f210,plain,(
% 1.74/0.60    k1_xboole_0 = sK1 | ~spl4_11),
% 1.74/0.60    inference(avatar_component_clause,[],[f209])).
% 1.74/0.60  fof(f209,plain,(
% 1.74/0.60    spl4_11 <=> k1_xboole_0 = sK1),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.74/0.60  fof(f159,plain,(
% 1.74/0.60    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 1.74/0.60    inference(avatar_component_clause,[],[f158])).
% 1.74/0.60  fof(f158,plain,(
% 1.74/0.60    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.74/0.60  fof(f1710,plain,(
% 1.74/0.60    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl4_119),
% 1.74/0.60    inference(avatar_component_clause,[],[f1709])).
% 1.74/0.60  fof(f1709,plain,(
% 1.74/0.60    spl4_119 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).
% 1.74/0.60  fof(f1501,plain,(
% 1.74/0.60    r1_tarski(k1_xboole_0,sK0) | (~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_58 | ~spl4_71)),
% 1.74/0.60    inference(backward_demodulation,[],[f767,f1493])).
% 1.74/0.60  fof(f1493,plain,(
% 1.74/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71)),
% 1.74/0.60    inference(backward_demodulation,[],[f1398,f940])).
% 1.74/0.60  fof(f1398,plain,(
% 1.74/0.60    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_11 | ~spl4_29 | ~spl4_40)),
% 1.74/0.60    inference(backward_demodulation,[],[f459,f1367])).
% 1.74/0.60  fof(f1367,plain,(
% 1.74/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29)),
% 1.74/0.60    inference(backward_demodulation,[],[f1242,f356])).
% 1.74/0.60  fof(f1242,plain,(
% 1.74/0.60    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_11),
% 1.74/0.60    inference(backward_demodulation,[],[f337,f210])).
% 1.74/0.60  fof(f337,plain,(
% 1.74/0.60    sK1 = k2_relat_1(sK2)),
% 1.74/0.60    inference(forward_demodulation,[],[f196,f87])).
% 1.74/0.60  fof(f87,plain,(
% 1.74/0.60    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f74])).
% 1.74/0.60  fof(f74,plain,(
% 1.74/0.60    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f73])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f36,plain,(
% 1.74/0.60    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.74/0.60    inference(flattening,[],[f35])).
% 1.74/0.60  fof(f35,plain,(
% 1.74/0.60    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.74/0.60    inference(ennf_transformation,[],[f34])).
% 1.74/0.60  fof(f34,negated_conjecture,(
% 1.74/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.74/0.60    inference(negated_conjecture,[],[f33])).
% 1.74/0.60  fof(f33,conjecture,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.74/0.60  fof(f196,plain,(
% 1.74/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.74/0.60    inference(resolution,[],[f85,f129])).
% 1.74/0.60  fof(f129,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f64])).
% 1.74/0.60  fof(f64,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f26])).
% 1.74/0.60  fof(f26,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.74/0.60  fof(f85,plain,(
% 1.74/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.74/0.60    inference(cnf_transformation,[],[f74])).
% 1.74/0.60  fof(f459,plain,(
% 1.74/0.60    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_40),
% 1.74/0.60    inference(avatar_component_clause,[],[f458])).
% 1.74/0.60  fof(f458,plain,(
% 1.74/0.60    spl4_40 <=> k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.74/0.60  fof(f767,plain,(
% 1.74/0.60    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~spl4_58),
% 1.74/0.60    inference(avatar_component_clause,[],[f766])).
% 1.74/0.60  fof(f766,plain,(
% 1.74/0.60    spl4_58 <=> r1_tarski(k1_relat_1(k1_xboole_0),sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.74/0.60  fof(f1711,plain,(
% 1.74/0.60    ~spl4_39 | ~spl4_117 | spl4_119 | ~spl4_118),
% 1.74/0.60    inference(avatar_split_clause,[],[f1696,f1529,f1709,f1524,f455])).
% 1.74/0.60  fof(f455,plain,(
% 1.74/0.60    spl4_39 <=> v1_funct_1(k1_xboole_0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.74/0.60  fof(f1524,plain,(
% 1.74/0.60    spl4_117 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).
% 1.74/0.60  fof(f1529,plain,(
% 1.74/0.60    spl4_118 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).
% 1.74/0.60  fof(f1696,plain,(
% 1.74/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)) ) | ~spl4_118),
% 1.74/0.60    inference(resolution,[],[f1530,f152])).
% 1.74/0.60  fof(f152,plain,(
% 1.74/0.60    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(X1,X2) | v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 1.74/0.60    inference(equality_resolution,[],[f139])).
% 1.74/0.60  fof(f139,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f72])).
% 1.74/0.60  fof(f72,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.74/0.60    inference(flattening,[],[f71])).
% 1.74/0.60  fof(f71,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.74/0.60    inference(ennf_transformation,[],[f32])).
% 1.74/0.60  fof(f32,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 1.74/0.60  fof(f1530,plain,(
% 1.74/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_118),
% 1.74/0.60    inference(avatar_component_clause,[],[f1529])).
% 1.74/0.60  fof(f1531,plain,(
% 1.74/0.60    ~spl4_37 | ~spl4_39 | spl4_118 | ~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71),
% 1.74/0.60    inference(avatar_split_clause,[],[f1527,f939,f458,f355,f209,f1529,f455,f445])).
% 1.74/0.60  fof(f445,plain,(
% 1.74/0.60    spl4_37 <=> v1_relat_1(k1_xboole_0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.74/0.60  fof(f1527,plain,(
% 1.74/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71)),
% 1.74/0.60    inference(forward_demodulation,[],[f1506,f1367])).
% 1.74/0.60  fof(f1506,plain,(
% 1.74/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71)),
% 1.74/0.60    inference(superposition,[],[f108,f1493])).
% 1.74/0.60  fof(f108,plain,(
% 1.74/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f44])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f43])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f31])).
% 1.74/0.60  fof(f31,axiom,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.74/0.60  fof(f1526,plain,(
% 1.74/0.60    ~spl4_37 | ~spl4_39 | spl4_117 | ~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71),
% 1.74/0.60    inference(avatar_split_clause,[],[f1522,f939,f458,f355,f209,f1524,f455,f445])).
% 1.74/0.60  fof(f1522,plain,(
% 1.74/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71)),
% 1.74/0.60    inference(forward_demodulation,[],[f1505,f1367])).
% 1.74/0.60  fof(f1505,plain,(
% 1.74/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29 | ~spl4_40 | ~spl4_71)),
% 1.74/0.60    inference(superposition,[],[f107,f1493])).
% 1.74/0.60  fof(f107,plain,(
% 1.74/0.60    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f44])).
% 1.74/0.60  fof(f1423,plain,(
% 1.74/0.60    ~spl4_37 | spl4_76 | ~spl4_11 | ~spl4_29),
% 1.74/0.60    inference(avatar_split_clause,[],[f1405,f355,f209,f969,f445])).
% 1.74/0.60  fof(f969,plain,(
% 1.74/0.60    spl4_76 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 1.74/0.60  fof(f1405,plain,(
% 1.74/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29)),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f1403])).
% 1.74/0.60  fof(f1403,plain,(
% 1.74/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_29)),
% 1.74/0.60    inference(superposition,[],[f105,f1367])).
% 1.74/0.60  fof(f105,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f75])).
% 1.74/0.60  fof(f75,plain,(
% 1.74/0.60    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(nnf_transformation,[],[f42])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f11])).
% 1.74/0.60  fof(f11,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.74/0.60  fof(f1386,plain,(
% 1.74/0.60    ~spl4_37 | spl4_58 | ~spl4_29),
% 1.74/0.60    inference(avatar_split_clause,[],[f1385,f355,f766,f445])).
% 1.74/0.60  fof(f1385,plain,(
% 1.74/0.60    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0) | ~spl4_29),
% 1.74/0.60    inference(resolution,[],[f1345,f118])).
% 1.74/0.60  fof(f118,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f76])).
% 1.74/0.60  fof(f76,plain,(
% 1.74/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(nnf_transformation,[],[f58])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f6])).
% 1.74/0.60  fof(f6,axiom,(
% 1.74/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.74/0.60  fof(f1345,plain,(
% 1.74/0.60    v4_relat_1(k1_xboole_0,sK0) | ~spl4_29),
% 1.74/0.60    inference(backward_demodulation,[],[f197,f356])).
% 1.74/0.60  fof(f197,plain,(
% 1.74/0.60    v4_relat_1(sK2,sK0)),
% 1.74/0.60    inference(resolution,[],[f85,f130])).
% 1.74/0.60  fof(f130,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f65])).
% 1.74/0.60  fof(f65,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f25])).
% 1.74/0.60  fof(f25,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.74/0.60  fof(f1288,plain,(
% 1.74/0.60    ~spl4_37 | spl4_38 | ~spl4_39),
% 1.74/0.60    inference(avatar_split_clause,[],[f1287,f455,f448,f445])).
% 1.74/0.60  fof(f448,plain,(
% 1.74/0.60    spl4_38 <=> v1_relat_1(k2_funct_1(k1_xboole_0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.74/0.60  fof(f1287,plain,(
% 1.74/0.60    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl4_39),
% 1.74/0.60    inference(resolution,[],[f578,f109])).
% 1.74/0.60  fof(f109,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f46])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f45])).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f15])).
% 1.74/0.60  fof(f15,axiom,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.74/0.60  fof(f578,plain,(
% 1.74/0.60    v1_funct_1(k1_xboole_0) | ~spl4_39),
% 1.74/0.60    inference(avatar_component_clause,[],[f455])).
% 1.74/0.60  fof(f1228,plain,(
% 1.74/0.60    spl4_29 | ~spl4_11),
% 1.74/0.60    inference(avatar_split_clause,[],[f1227,f209,f355])).
% 1.74/0.60  fof(f1227,plain,(
% 1.74/0.60    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 1.74/0.60    inference(global_subsumption,[],[f195,f807])).
% 1.74/0.60  fof(f807,plain,(
% 1.74/0.60    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.74/0.60    inference(superposition,[],[f103,f337])).
% 1.74/0.60  fof(f103,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f10])).
% 1.74/0.60  fof(f10,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.74/0.60  fof(f195,plain,(
% 1.74/0.60    v1_relat_1(sK2)),
% 1.74/0.60    inference(resolution,[],[f85,f128])).
% 1.74/0.60  fof(f128,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f63])).
% 1.74/0.60  fof(f63,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f24])).
% 1.74/0.60  fof(f24,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.74/0.60  fof(f1220,plain,(
% 1.74/0.60    ~spl4_32 | ~spl4_96),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1216])).
% 1.74/0.60  fof(f1216,plain,(
% 1.74/0.60    $false | (~spl4_32 | ~spl4_96)),
% 1.74/0.60    inference(subsumption_resolution,[],[f376,f1206])).
% 1.74/0.60  fof(f1206,plain,(
% 1.74/0.60    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl4_96),
% 1.74/0.60    inference(avatar_component_clause,[],[f1205])).
% 1.74/0.60  fof(f1205,plain,(
% 1.74/0.60    spl4_96 <=> ! [X0] : ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 1.74/0.60  fof(f376,plain,(
% 1.74/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl4_32),
% 1.74/0.60    inference(avatar_component_clause,[],[f375])).
% 1.74/0.60  fof(f375,plain,(
% 1.74/0.60    spl4_32 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.74/0.60  fof(f1214,plain,(
% 1.74/0.60    spl4_97),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1212])).
% 1.74/0.60  fof(f1212,plain,(
% 1.74/0.60    $false | spl4_97),
% 1.74/0.60    inference(subsumption_resolution,[],[f1209,f237])).
% 1.74/0.60  fof(f237,plain,(
% 1.74/0.60    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.74/0.60    inference(global_subsumption,[],[f195,f236])).
% 1.74/0.60  fof(f236,plain,(
% 1.74/0.60    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.74/0.60    inference(resolution,[],[f197,f118])).
% 1.74/0.60  fof(f1209,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_97),
% 1.74/0.60    inference(avatar_component_clause,[],[f1208])).
% 1.74/0.60  fof(f1208,plain,(
% 1.74/0.60    spl4_97 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 1.74/0.60  fof(f1210,plain,(
% 1.74/0.60    spl4_96 | ~spl4_97 | spl4_3 | ~spl4_7),
% 1.74/0.60    inference(avatar_split_clause,[],[f1203,f182,f161,f1208,f1205])).
% 1.74/0.60  fof(f161,plain,(
% 1.74/0.60    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.74/0.60  fof(f182,plain,(
% 1.74/0.60    spl4_7 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.74/0.60  fof(f1203,plain,(
% 1.74/0.60    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (spl4_3 | ~spl4_7)),
% 1.74/0.60    inference(forward_demodulation,[],[f1201,f183])).
% 1.74/0.60  fof(f183,plain,(
% 1.74/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.74/0.60    inference(avatar_component_clause,[],[f182])).
% 1.74/0.60  fof(f1201,plain,(
% 1.74/0.60    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl4_3),
% 1.74/0.60    inference(resolution,[],[f162,f135])).
% 1.74/0.60  fof(f135,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f70])).
% 1.74/0.60  fof(f70,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.74/0.60    inference(flattening,[],[f69])).
% 1.74/0.60  fof(f69,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.74/0.60    inference(ennf_transformation,[],[f27])).
% 1.74/0.60  fof(f27,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 1.74/0.60  fof(f162,plain,(
% 1.74/0.60    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 1.74/0.60    inference(avatar_component_clause,[],[f161])).
% 1.74/0.60  fof(f1200,plain,(
% 1.74/0.60    spl4_2 | ~spl4_87),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1198])).
% 1.74/0.60  fof(f1198,plain,(
% 1.74/0.60    $false | (spl4_2 | ~spl4_87)),
% 1.74/0.60    inference(subsumption_resolution,[],[f237,f1197])).
% 1.74/0.60  fof(f1197,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl4_2 | ~spl4_87)),
% 1.74/0.60    inference(resolution,[],[f1103,f159])).
% 1.74/0.61  fof(f1103,plain,(
% 1.74/0.61    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl4_87),
% 1.74/0.61    inference(avatar_component_clause,[],[f1102])).
% 1.74/0.61  fof(f1102,plain,(
% 1.74/0.61    spl4_87 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 1.74/0.61  fof(f1104,plain,(
% 1.74/0.61    ~spl4_1 | ~spl4_31 | spl4_87 | spl4_28 | ~spl4_32),
% 1.74/0.61    inference(avatar_split_clause,[],[f1095,f375,f332,f1102,f370,f155])).
% 1.74/0.61  % (9800)Refutation not found, incomplete strategy% (9800)------------------------------
% 1.74/0.61  % (9800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (9800)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.61  
% 1.74/0.61  % (9800)Memory used [KB]: 6652
% 1.74/0.61  % (9800)Time elapsed: 0.173 s
% 1.74/0.61  % (9800)------------------------------
% 1.74/0.61  % (9800)------------------------------
% 1.74/0.61  fof(f155,plain,(
% 1.74/0.61    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.74/0.61  fof(f370,plain,(
% 1.74/0.61    spl4_31 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.74/0.61  fof(f332,plain,(
% 1.74/0.61    spl4_28 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.74/0.61  fof(f1095,plain,(
% 1.74/0.61    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl4_32),
% 1.74/0.61    inference(resolution,[],[f376,f138])).
% 1.74/0.61  fof(f138,plain,(
% 1.74/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f72])).
% 1.74/0.61  fof(f973,plain,(
% 1.74/0.61    ~spl4_38 | spl4_71 | ~spl4_76 | ~spl4_41),
% 1.74/0.61    inference(avatar_split_clause,[],[f948,f462,f969,f939,f448])).
% 1.74/0.61  fof(f462,plain,(
% 1.74/0.61    spl4_41 <=> k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.74/0.61  fof(f948,plain,(
% 1.74/0.61    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_41),
% 1.74/0.61    inference(superposition,[],[f103,f463])).
% 1.74/0.61  fof(f463,plain,(
% 1.74/0.61    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_41),
% 1.74/0.61    inference(avatar_component_clause,[],[f462])).
% 1.74/0.61  fof(f900,plain,(
% 1.74/0.61    ~spl4_5 | spl4_23 | ~spl4_28 | ~spl4_7),
% 1.74/0.61    inference(avatar_split_clause,[],[f891,f182,f332,f303,f169])).
% 1.74/0.61  fof(f169,plain,(
% 1.74/0.61    spl4_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.74/0.61  fof(f303,plain,(
% 1.74/0.61    spl4_23 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.74/0.61  fof(f891,plain,(
% 1.74/0.61    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.74/0.61    inference(superposition,[],[f103,f183])).
% 1.74/0.61  fof(f899,plain,(
% 1.74/0.61    ~spl4_5 | ~spl4_28 | spl4_11 | ~spl4_6 | ~spl4_7),
% 1.74/0.61    inference(avatar_split_clause,[],[f898,f182,f177,f209,f332,f169])).
% 1.74/0.61  fof(f177,plain,(
% 1.74/0.61    spl4_6 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.74/0.61  fof(f898,plain,(
% 1.74/0.61    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_6 | ~spl4_7)),
% 1.74/0.61    inference(forward_demodulation,[],[f890,f338])).
% 1.74/0.61  fof(f338,plain,(
% 1.74/0.61    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_6),
% 1.74/0.61    inference(backward_demodulation,[],[f178,f337])).
% 1.74/0.61  fof(f178,plain,(
% 1.74/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_6),
% 1.74/0.61    inference(avatar_component_clause,[],[f177])).
% 1.74/0.61  fof(f890,plain,(
% 1.74/0.61    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.74/0.61    inference(superposition,[],[f105,f183])).
% 1.74/0.61  fof(f897,plain,(
% 1.74/0.61    ~spl4_5 | ~spl4_1 | spl4_32 | ~spl4_6 | ~spl4_7),
% 1.74/0.61    inference(avatar_split_clause,[],[f896,f182,f177,f375,f155,f169])).
% 1.74/0.61  fof(f896,plain,(
% 1.74/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_6 | ~spl4_7)),
% 1.74/0.61    inference(forward_demodulation,[],[f889,f338])).
% 1.74/0.61  fof(f889,plain,(
% 1.74/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.74/0.61    inference(superposition,[],[f108,f183])).
% 1.74/0.61  fof(f895,plain,(
% 1.74/0.61    ~spl4_5 | ~spl4_1 | spl4_31 | ~spl4_6 | ~spl4_7),
% 1.74/0.61    inference(avatar_split_clause,[],[f894,f182,f177,f370,f155,f169])).
% 1.74/0.61  fof(f894,plain,(
% 1.74/0.61    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_6 | ~spl4_7)),
% 1.74/0.61    inference(forward_demodulation,[],[f888,f338])).
% 1.74/0.61  fof(f888,plain,(
% 1.74/0.61    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.74/0.61    inference(superposition,[],[f107,f183])).
% 1.74/0.61  fof(f735,plain,(
% 1.74/0.61    ~spl4_37 | ~spl4_39 | spl4_41 | ~spl4_29),
% 1.74/0.61    inference(avatar_split_clause,[],[f732,f355,f462,f455,f445])).
% 1.74/0.61  fof(f732,plain,(
% 1.74/0.61    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_29),
% 1.74/0.61    inference(resolution,[],[f722,f113])).
% 1.74/0.61  fof(f113,plain,(
% 1.74/0.61    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f50])).
% 1.74/0.61  fof(f50,plain,(
% 1.74/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.61    inference(flattening,[],[f49])).
% 1.74/0.61  fof(f49,plain,(
% 1.74/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f20])).
% 1.74/0.61  fof(f20,axiom,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.74/0.61  fof(f722,plain,(
% 1.74/0.61    v2_funct_1(k1_xboole_0) | ~spl4_29),
% 1.74/0.61    inference(backward_demodulation,[],[f86,f356])).
% 1.74/0.61  fof(f86,plain,(
% 1.74/0.61    v2_funct_1(sK2)),
% 1.74/0.61    inference(cnf_transformation,[],[f74])).
% 1.74/0.61  fof(f734,plain,(
% 1.74/0.61    ~spl4_37 | ~spl4_39 | spl4_40 | ~spl4_29),
% 1.74/0.61    inference(avatar_split_clause,[],[f731,f355,f458,f455,f445])).
% 1.74/0.61  fof(f731,plain,(
% 1.74/0.61    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_29),
% 1.74/0.61    inference(resolution,[],[f722,f112])).
% 1.74/0.61  fof(f112,plain,(
% 1.74/0.61    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f50])).
% 1.74/0.61  fof(f579,plain,(
% 1.74/0.61    ~spl4_4 | ~spl4_9 | spl4_39 | ~spl4_23),
% 1.74/0.61    inference(avatar_split_clause,[],[f577,f303,f455,f192,f166])).
% 1.74/0.61  fof(f166,plain,(
% 1.74/0.61    spl4_4 <=> v1_relat_1(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.74/0.61  fof(f192,plain,(
% 1.74/0.61    spl4_9 <=> v1_funct_1(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.74/0.61  fof(f577,plain,(
% 1.74/0.61    v1_funct_1(k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_23),
% 1.74/0.61    inference(superposition,[],[f110,f304])).
% 1.74/0.61  fof(f304,plain,(
% 1.74/0.61    k1_xboole_0 = k2_funct_1(sK2) | ~spl4_23),
% 1.74/0.61    inference(avatar_component_clause,[],[f303])).
% 1.74/0.61  fof(f110,plain,(
% 1.74/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f46])).
% 1.74/0.61  fof(f473,plain,(
% 1.74/0.61    ~spl4_29 | spl4_37),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f472])).
% 1.74/0.61  fof(f472,plain,(
% 1.74/0.61    $false | (~spl4_29 | spl4_37)),
% 1.74/0.61    inference(subsumption_resolution,[],[f435,f446])).
% 1.74/0.61  fof(f446,plain,(
% 1.74/0.61    ~v1_relat_1(k1_xboole_0) | spl4_37),
% 1.74/0.61    inference(avatar_component_clause,[],[f445])).
% 1.74/0.61  fof(f435,plain,(
% 1.74/0.61    v1_relat_1(k1_xboole_0) | ~spl4_29),
% 1.74/0.61    inference(backward_demodulation,[],[f195,f356])).
% 1.74/0.61  fof(f230,plain,(
% 1.74/0.61    spl4_9),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f229])).
% 1.74/0.61  fof(f229,plain,(
% 1.74/0.61    $false | spl4_9),
% 1.74/0.61    inference(subsumption_resolution,[],[f83,f193])).
% 1.74/0.61  fof(f193,plain,(
% 1.74/0.61    ~v1_funct_1(sK2) | spl4_9),
% 1.74/0.61    inference(avatar_component_clause,[],[f192])).
% 1.74/0.61  fof(f83,plain,(
% 1.74/0.61    v1_funct_1(sK2)),
% 1.74/0.61    inference(cnf_transformation,[],[f74])).
% 1.74/0.61  fof(f228,plain,(
% 1.74/0.61    spl4_4),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f224])).
% 1.74/0.61  fof(f224,plain,(
% 1.74/0.61    $false | spl4_4),
% 1.74/0.61    inference(subsumption_resolution,[],[f167,f195])).
% 1.74/0.61  fof(f167,plain,(
% 1.74/0.61    ~v1_relat_1(sK2) | spl4_4),
% 1.74/0.61    inference(avatar_component_clause,[],[f166])).
% 1.74/0.61  fof(f194,plain,(
% 1.74/0.61    ~spl4_4 | ~spl4_9 | spl4_1),
% 1.74/0.61    inference(avatar_split_clause,[],[f190,f155,f192,f166])).
% 1.74/0.61  fof(f190,plain,(
% 1.74/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 1.74/0.61    inference(resolution,[],[f156,f110])).
% 1.74/0.61  fof(f156,plain,(
% 1.74/0.61    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 1.74/0.61    inference(avatar_component_clause,[],[f155])).
% 1.74/0.61  fof(f184,plain,(
% 1.74/0.61    ~spl4_4 | spl4_7),
% 1.74/0.61    inference(avatar_split_clause,[],[f180,f182,f166])).
% 1.74/0.61  fof(f180,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(global_subsumption,[],[f83,f173])).
% 1.74/0.61  fof(f173,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f86,f113])).
% 1.74/0.61  fof(f179,plain,(
% 1.74/0.61    ~spl4_4 | spl4_6),
% 1.74/0.61    inference(avatar_split_clause,[],[f175,f177,f166])).
% 1.74/0.61  fof(f175,plain,(
% 1.74/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(global_subsumption,[],[f83,f172])).
% 1.74/0.61  fof(f172,plain,(
% 1.74/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f86,f112])).
% 1.74/0.61  fof(f171,plain,(
% 1.74/0.61    ~spl4_4 | spl4_5),
% 1.74/0.61    inference(avatar_split_clause,[],[f164,f169,f166])).
% 1.74/0.61  fof(f164,plain,(
% 1.74/0.61    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f83,f109])).
% 1.74/0.61  fof(f163,plain,(
% 1.74/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.74/0.61    inference(avatar_split_clause,[],[f88,f161,f158,f155])).
% 1.74/0.61  fof(f88,plain,(
% 1.74/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f74])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (9798)------------------------------
% 1.74/0.61  % (9798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (9798)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (9798)Memory used [KB]: 11513
% 1.74/0.61  % (9798)Time elapsed: 0.143 s
% 1.74/0.61  % (9798)------------------------------
% 1.74/0.61  % (9798)------------------------------
% 1.74/0.61  % (9795)Success in time 0.233 s
%------------------------------------------------------------------------------
