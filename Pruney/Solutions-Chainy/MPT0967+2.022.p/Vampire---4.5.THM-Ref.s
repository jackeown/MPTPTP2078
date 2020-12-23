%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:45 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 367 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 (1336 expanded)
%              Number of equality atoms :   85 ( 380 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f211,f931,f949,f1212,f1552,f1635,f1645,f1853,f2086])).

fof(f2086,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f2079])).

fof(f2079,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f63,f2074,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2074,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f2069,f98])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2069,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f1910,f1886,f102])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1886,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f1858,f1630])).

fof(f1630,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f1628,plain,
    ( spl7_14
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f1858,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f1440,f1647])).

fof(f1647,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1646,f98])).

% (9807)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f1646,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f926,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f926,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f924])).

fof(f924,plain,
    ( spl7_12
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1440,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f954,f139])).

fof(f954,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f201,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f201,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1910,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_1
    | spl7_4
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1435,f1647])).

fof(f1435,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl7_1
    | spl7_4 ),
    inference(backward_demodulation,[],[f206,f139])).

fof(f206,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1853,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f1850])).

fof(f1850,plain,
    ( $false
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f51,f210])).

fof(f210,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl7_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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

fof(f1645,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f1638])).

fof(f1638,plain,
    ( $false
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f63,f1634,f67])).

fof(f1634,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f1632,plain,
    ( spl7_15
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1635,plain,
    ( spl7_14
    | ~ spl7_15
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f1571,f141,f137,f1632,f1628])).

fof(f141,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1571,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f1570,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1570,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f1566,f1514])).

fof(f1514,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f1447,f1469])).

fof(f1469,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f63,f1330,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1330,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f1231,f97])).

fof(f1231,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f172,f142])).

fof(f142,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f172,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f53,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f1447,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f1233,f139])).

fof(f1233,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f174,f142])).

fof(f174,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f91])).

fof(f1566,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f1513,f101])).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1513,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f1446,f1469])).

fof(f1446,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f1216,f139])).

fof(f1216,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f52,f142])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f1552,plain,
    ( ~ spl7_2
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f1544])).

fof(f1544,plain,
    ( $false
    | ~ spl7_2
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f533,f1504,f68])).

fof(f1504,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | spl7_13 ),
    inference(backward_demodulation,[],[f1427,f1469])).

fof(f1427,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_2
    | spl7_13 ),
    inference(forward_demodulation,[],[f1317,f97])).

fof(f1317,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | ~ spl7_2
    | spl7_13 ),
    inference(backward_demodulation,[],[f930,f142])).

fof(f930,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f928])).

fof(f928,plain,
    ( spl7_13
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f533,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f530,f97])).

fof(f530,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) ),
    inference(superposition,[],[f346,f97])).

fof(f346,plain,(
    ! [X0] : m1_subset_1(k2_zfmisc_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    inference(unit_resulting_resolution,[],[f107,f67])).

fof(f107,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f54,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f54,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1212,plain,
    ( spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1204])).

fof(f1204,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f64,f533,f985,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f985,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(backward_demodulation,[],[f157,f968])).

fof(f968,plain,
    ( k1_xboole_0 = sK2
    | spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f206,f201,f959,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f959,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f950,f179])).

fof(f179,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl7_2 ),
    inference(forward_demodulation,[],[f169,f170])).

fof(f170,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f143,f52,f53,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f143,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f169,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f53,f91])).

fof(f950,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f201,f91])).

fof(f157,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f109,f154,f76])).

fof(f154,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f64,f143,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f109,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f54,f67])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f949,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f947])).

fof(f947,plain,
    ( $false
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f388,f320,f67])).

fof(f320,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f202,f173,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f173,plain,(
    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f77,f53,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f77,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f202,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f200])).

fof(f388,plain,(
    ! [X0] : r1_tarski(k1_zfmisc_1(k2_zfmisc_1(X0,sK1)),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f108,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f108,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f54,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f931,plain,
    ( spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f254,f928,f924])).

fof(f254,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f172,f61])).

fof(f211,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f49,f208,f204,f200])).

fof(f49,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f144,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f50,f141,f137])).

fof(f50,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (9776)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (9794)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (9776)Refutation not found, incomplete strategy% (9776)------------------------------
% 0.22/0.52  % (9776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9786)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (9776)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9776)Memory used [KB]: 10746
% 0.22/0.52  % (9776)Time elapsed: 0.103 s
% 0.22/0.52  % (9776)------------------------------
% 0.22/0.52  % (9776)------------------------------
% 0.22/0.52  % (9783)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (9797)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (9801)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (9793)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (9789)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (9777)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (9798)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (9775)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (9778)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (9774)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (9780)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (9784)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (9781)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (9803)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (9802)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (9790)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (9799)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (9795)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (9800)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (9785)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (9782)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (9782)Refutation not found, incomplete strategy% (9782)------------------------------
% 0.22/0.56  % (9782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9782)Memory used [KB]: 10746
% 0.22/0.56  % (9782)Time elapsed: 0.150 s
% 0.22/0.56  % (9782)------------------------------
% 0.22/0.56  % (9782)------------------------------
% 0.22/0.56  % (9791)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (9779)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (9787)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (9792)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.58  % (9788)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (9796)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.62  % (9796)Refutation not found, incomplete strategy% (9796)------------------------------
% 0.22/0.62  % (9796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.63  % (9796)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.63  
% 1.89/0.63  % (9796)Memory used [KB]: 10874
% 1.89/0.63  % (9796)Time elapsed: 0.170 s
% 1.89/0.63  % (9796)------------------------------
% 1.89/0.63  % (9796)------------------------------
% 2.15/0.66  % (9778)Refutation found. Thanks to Tanya!
% 2.15/0.66  % SZS status Theorem for theBenchmark
% 2.15/0.66  % SZS output start Proof for theBenchmark
% 2.15/0.66  fof(f2087,plain,(
% 2.15/0.66    $false),
% 2.15/0.66    inference(avatar_sat_refutation,[],[f144,f211,f931,f949,f1212,f1552,f1635,f1645,f1853,f2086])).
% 2.15/0.66  fof(f2086,plain,(
% 2.15/0.66    ~spl7_1 | ~spl7_3 | spl7_4 | ~spl7_12 | ~spl7_14),
% 2.15/0.66    inference(avatar_contradiction_clause,[],[f2079])).
% 2.15/0.66  fof(f2079,plain,(
% 2.15/0.66    $false | (~spl7_1 | ~spl7_3 | spl7_4 | ~spl7_12 | ~spl7_14)),
% 2.15/0.66    inference(unit_resulting_resolution,[],[f63,f2074,f67])).
% 2.15/0.66  fof(f67,plain,(
% 2.15/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f16])).
% 2.15/0.66  fof(f16,axiom,(
% 2.15/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.15/0.66  fof(f2074,plain,(
% 2.15/0.66    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_1 | ~spl7_3 | spl7_4 | ~spl7_12 | ~spl7_14)),
% 2.15/0.66    inference(forward_demodulation,[],[f2069,f98])).
% 2.15/0.66  fof(f98,plain,(
% 2.15/0.66    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.15/0.66    inference(equality_resolution,[],[f57])).
% 2.15/0.66  fof(f57,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f10])).
% 2.15/0.66  fof(f10,axiom,(
% 2.15/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.15/0.66  fof(f2069,plain,(
% 2.15/0.66    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (~spl7_1 | ~spl7_3 | spl7_4 | ~spl7_12 | ~spl7_14)),
% 2.15/0.66    inference(unit_resulting_resolution,[],[f1910,f1886,f102])).
% 2.15/0.66  fof(f102,plain,(
% 2.15/0.66    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 2.15/0.66    inference(equality_resolution,[],[f80])).
% 2.15/0.66  fof(f80,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f43])).
% 2.15/0.66  fof(f43,plain,(
% 2.15/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(flattening,[],[f42])).
% 2.15/0.66  fof(f42,plain,(
% 2.15/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(ennf_transformation,[],[f24])).
% 2.15/0.66  fof(f24,axiom,(
% 2.15/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.15/0.66  fof(f1886,plain,(
% 2.15/0.66    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl7_1 | ~spl7_3 | ~spl7_12 | ~spl7_14)),
% 2.15/0.66    inference(forward_demodulation,[],[f1858,f1630])).
% 2.15/0.66  fof(f1630,plain,(
% 2.15/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_14),
% 2.15/0.66    inference(avatar_component_clause,[],[f1628])).
% 2.15/0.66  fof(f1628,plain,(
% 2.15/0.66    spl7_14 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.15/0.66  fof(f1858,plain,(
% 2.15/0.66    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl7_1 | ~spl7_3 | ~spl7_12)),
% 2.15/0.66    inference(backward_demodulation,[],[f1440,f1647])).
% 2.15/0.66  fof(f1647,plain,(
% 2.15/0.66    k1_xboole_0 = sK3 | (~spl7_1 | ~spl7_12)),
% 2.15/0.66    inference(forward_demodulation,[],[f1646,f98])).
% 2.27/0.67  % (9807)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.27/0.68  fof(f1646,plain,(
% 2.27/0.68    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl7_1 | ~spl7_12)),
% 2.27/0.68    inference(forward_demodulation,[],[f926,f139])).
% 2.27/0.68  fof(f139,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~spl7_1),
% 2.27/0.68    inference(avatar_component_clause,[],[f137])).
% 2.27/0.68  fof(f137,plain,(
% 2.27/0.68    spl7_1 <=> k1_xboole_0 = sK0),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.27/0.68  fof(f926,plain,(
% 2.27/0.68    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl7_12),
% 2.27/0.68    inference(avatar_component_clause,[],[f924])).
% 2.27/0.68  fof(f924,plain,(
% 2.27/0.68    spl7_12 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.27/0.68  fof(f1440,plain,(
% 2.27/0.68    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl7_1 | ~spl7_3)),
% 2.27/0.68    inference(backward_demodulation,[],[f954,f139])).
% 2.27/0.68  fof(f954,plain,(
% 2.27/0.68    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl7_3),
% 2.27/0.68    inference(resolution,[],[f201,f91])).
% 2.27/0.68  fof(f91,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f45])).
% 2.27/0.68  fof(f45,plain,(
% 2.27/0.68    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.68    inference(ennf_transformation,[],[f23])).
% 2.27/0.68  fof(f23,axiom,(
% 2.27/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.27/0.68  fof(f201,plain,(
% 2.27/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl7_3),
% 2.27/0.68    inference(avatar_component_clause,[],[f200])).
% 2.27/0.68  fof(f200,plain,(
% 2.27/0.68    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.27/0.68  fof(f1910,plain,(
% 2.27/0.68    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_1 | spl7_4 | ~spl7_12)),
% 2.27/0.68    inference(forward_demodulation,[],[f1435,f1647])).
% 2.27/0.68  fof(f1435,plain,(
% 2.27/0.68    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl7_1 | spl7_4)),
% 2.27/0.68    inference(backward_demodulation,[],[f206,f139])).
% 2.27/0.68  fof(f206,plain,(
% 2.27/0.68    ~v1_funct_2(sK3,sK0,sK2) | spl7_4),
% 2.27/0.68    inference(avatar_component_clause,[],[f204])).
% 2.27/0.68  fof(f204,plain,(
% 2.27/0.68    spl7_4 <=> v1_funct_2(sK3,sK0,sK2)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.27/0.68  fof(f63,plain,(
% 2.27/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f7])).
% 2.27/0.68  fof(f7,axiom,(
% 2.27/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.27/0.68  fof(f1853,plain,(
% 2.27/0.68    spl7_5),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1850])).
% 2.27/0.68  fof(f1850,plain,(
% 2.27/0.68    $false | spl7_5),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f51,f210])).
% 2.27/0.68  fof(f210,plain,(
% 2.27/0.68    ~v1_funct_1(sK3) | spl7_5),
% 2.27/0.68    inference(avatar_component_clause,[],[f208])).
% 2.27/0.68  fof(f208,plain,(
% 2.27/0.68    spl7_5 <=> v1_funct_1(sK3)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.27/0.68  fof(f51,plain,(
% 2.27/0.68    v1_funct_1(sK3)),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  fof(f30,plain,(
% 2.27/0.68    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.27/0.68    inference(flattening,[],[f29])).
% 2.27/0.68  fof(f29,plain,(
% 2.27/0.68    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.27/0.68    inference(ennf_transformation,[],[f27])).
% 2.27/0.68  fof(f27,negated_conjecture,(
% 2.27/0.68    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.27/0.68    inference(negated_conjecture,[],[f26])).
% 2.27/0.68  fof(f26,conjecture,(
% 2.27/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 2.27/0.68  fof(f1645,plain,(
% 2.27/0.68    spl7_15),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1638])).
% 2.27/0.68  fof(f1638,plain,(
% 2.27/0.68    $false | spl7_15),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f63,f1634,f67])).
% 2.27/0.68  fof(f1634,plain,(
% 2.27/0.68    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl7_15),
% 2.27/0.68    inference(avatar_component_clause,[],[f1632])).
% 2.27/0.68  fof(f1632,plain,(
% 2.27/0.68    spl7_15 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.27/0.68  fof(f1635,plain,(
% 2.27/0.68    spl7_14 | ~spl7_15 | ~spl7_1 | ~spl7_2),
% 2.27/0.68    inference(avatar_split_clause,[],[f1571,f141,f137,f1632,f1628])).
% 2.27/0.68  fof(f141,plain,(
% 2.27/0.68    spl7_2 <=> k1_xboole_0 = sK1),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.27/0.68  fof(f1571,plain,(
% 2.27/0.68    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(forward_demodulation,[],[f1570,f97])).
% 2.27/0.68  fof(f97,plain,(
% 2.27/0.68    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.27/0.68    inference(equality_resolution,[],[f58])).
% 2.27/0.68  fof(f58,plain,(
% 2.27/0.68    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f10])).
% 2.27/0.68  fof(f1570,plain,(
% 2.27/0.68    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(forward_demodulation,[],[f1566,f1514])).
% 2.27/0.68  fof(f1514,plain,(
% 2.27/0.68    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(backward_demodulation,[],[f1447,f1469])).
% 2.27/0.68  fof(f1469,plain,(
% 2.27/0.68    k1_xboole_0 = sK3 | ~spl7_2),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f63,f1330,f61])).
% 2.27/0.68  fof(f61,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.27/0.68    inference(cnf_transformation,[],[f6])).
% 2.27/0.68  fof(f6,axiom,(
% 2.27/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.27/0.68  fof(f1330,plain,(
% 2.27/0.68    r1_tarski(sK3,k1_xboole_0) | ~spl7_2),
% 2.27/0.68    inference(forward_demodulation,[],[f1231,f97])).
% 2.27/0.68  fof(f1231,plain,(
% 2.27/0.68    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl7_2),
% 2.27/0.68    inference(backward_demodulation,[],[f172,f142])).
% 2.27/0.68  fof(f142,plain,(
% 2.27/0.68    k1_xboole_0 = sK1 | ~spl7_2),
% 2.27/0.68    inference(avatar_component_clause,[],[f141])).
% 2.27/0.68  fof(f172,plain,(
% 2.27/0.68    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f53,f68])).
% 2.27/0.68  fof(f68,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f16])).
% 2.27/0.68  fof(f53,plain,(
% 2.27/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  fof(f1447,plain,(
% 2.27/0.68    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(backward_demodulation,[],[f1233,f139])).
% 2.27/0.68  fof(f1233,plain,(
% 2.27/0.68    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl7_2),
% 2.27/0.68    inference(backward_demodulation,[],[f174,f142])).
% 2.27/0.68  fof(f174,plain,(
% 2.27/0.68    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 2.27/0.68    inference(resolution,[],[f53,f91])).
% 2.27/0.68  fof(f1566,plain,(
% 2.27/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(resolution,[],[f1513,f101])).
% 2.27/0.68  fof(f101,plain,(
% 2.27/0.68    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.27/0.68    inference(equality_resolution,[],[f81])).
% 2.27/0.68  fof(f81,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f43])).
% 2.27/0.68  fof(f1513,plain,(
% 2.27/0.68    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(backward_demodulation,[],[f1446,f1469])).
% 2.27/0.68  fof(f1446,plain,(
% 2.27/0.68    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 2.27/0.68    inference(backward_demodulation,[],[f1216,f139])).
% 2.27/0.68  fof(f1216,plain,(
% 2.27/0.68    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_2),
% 2.27/0.68    inference(backward_demodulation,[],[f52,f142])).
% 2.27/0.68  fof(f52,plain,(
% 2.27/0.68    v1_funct_2(sK3,sK0,sK1)),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  fof(f1552,plain,(
% 2.27/0.68    ~spl7_2 | spl7_13),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1544])).
% 2.27/0.68  fof(f1544,plain,(
% 2.27/0.68    $false | (~spl7_2 | spl7_13)),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f533,f1504,f68])).
% 2.27/0.68  fof(f1504,plain,(
% 2.27/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_2 | spl7_13)),
% 2.27/0.68    inference(backward_demodulation,[],[f1427,f1469])).
% 2.27/0.68  fof(f1427,plain,(
% 2.27/0.68    ~r1_tarski(k1_xboole_0,sK3) | (~spl7_2 | spl7_13)),
% 2.27/0.68    inference(forward_demodulation,[],[f1317,f97])).
% 2.27/0.68  fof(f1317,plain,(
% 2.27/0.68    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (~spl7_2 | spl7_13)),
% 2.27/0.68    inference(backward_demodulation,[],[f930,f142])).
% 2.27/0.68  fof(f930,plain,(
% 2.27/0.68    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl7_13),
% 2.27/0.68    inference(avatar_component_clause,[],[f928])).
% 2.27/0.68  fof(f928,plain,(
% 2.27/0.68    spl7_13 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.27/0.68  fof(f533,plain,(
% 2.27/0.68    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.27/0.68    inference(forward_demodulation,[],[f530,f97])).
% 2.27/0.68  fof(f530,plain,(
% 2.27/0.68    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))),
% 2.27/0.68    inference(superposition,[],[f346,f97])).
% 2.27/0.68  fof(f346,plain,(
% 2.27/0.68    ( ! [X0] : (m1_subset_1(k2_zfmisc_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) )),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f107,f67])).
% 2.27/0.68  fof(f107,plain,(
% 2.27/0.68    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X0))) )),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f54,f65])).
% 2.27/0.68  fof(f65,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f33])).
% 2.27/0.68  fof(f33,plain,(
% 2.27/0.68    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 2.27/0.68    inference(ennf_transformation,[],[f11])).
% 2.27/0.68  fof(f11,axiom,(
% 2.27/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 2.27/0.68  fof(f54,plain,(
% 2.27/0.68    r1_tarski(sK1,sK2)),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  fof(f1212,plain,(
% 2.27/0.68    spl7_2 | ~spl7_3 | spl7_4),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1204])).
% 2.27/0.68  fof(f1204,plain,(
% 2.27/0.68    $false | (spl7_2 | ~spl7_3 | spl7_4)),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f64,f533,f985,f76])).
% 2.27/0.68  fof(f76,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f41])).
% 2.27/0.68  fof(f41,plain,(
% 2.27/0.68    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.27/0.68    inference(ennf_transformation,[],[f14])).
% 2.27/0.68  fof(f14,axiom,(
% 2.27/0.68    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.27/0.68  fof(f985,plain,(
% 2.27/0.68    ~v1_xboole_0(k1_xboole_0) | (spl7_2 | ~spl7_3 | spl7_4)),
% 2.27/0.68    inference(backward_demodulation,[],[f157,f968])).
% 2.27/0.68  fof(f968,plain,(
% 2.27/0.68    k1_xboole_0 = sK2 | (spl7_2 | ~spl7_3 | spl7_4)),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f206,f201,f959,f82])).
% 2.27/0.68  fof(f82,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f43])).
% 2.27/0.68  fof(f959,plain,(
% 2.27/0.68    sK0 = k1_relset_1(sK0,sK2,sK3) | (spl7_2 | ~spl7_3)),
% 2.27/0.68    inference(forward_demodulation,[],[f950,f179])).
% 2.27/0.68  fof(f179,plain,(
% 2.27/0.68    sK0 = k1_relat_1(sK3) | spl7_2),
% 2.27/0.68    inference(forward_demodulation,[],[f169,f170])).
% 2.27/0.68  fof(f170,plain,(
% 2.27/0.68    sK0 = k1_relset_1(sK0,sK1,sK3) | spl7_2),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f143,f52,f53,f83])).
% 2.27/0.68  fof(f83,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f43])).
% 2.27/0.68  fof(f143,plain,(
% 2.27/0.68    k1_xboole_0 != sK1 | spl7_2),
% 2.27/0.68    inference(avatar_component_clause,[],[f141])).
% 2.27/0.68  fof(f169,plain,(
% 2.27/0.68    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f53,f91])).
% 2.27/0.68  fof(f950,plain,(
% 2.27/0.68    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl7_3),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f201,f91])).
% 2.27/0.68  fof(f157,plain,(
% 2.27/0.68    ~v1_xboole_0(sK2) | spl7_2),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f109,f154,f76])).
% 2.27/0.68  fof(f154,plain,(
% 2.27/0.68    ~v1_xboole_0(sK1) | spl7_2),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f64,f143,f55])).
% 2.27/0.68  fof(f55,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f31])).
% 2.27/0.68  fof(f31,plain,(
% 2.27/0.68    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.27/0.68    inference(ennf_transformation,[],[f9])).
% 2.27/0.68  fof(f9,axiom,(
% 2.27/0.68    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.27/0.68  fof(f109,plain,(
% 2.27/0.68    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f54,f67])).
% 2.27/0.68  fof(f64,plain,(
% 2.27/0.68    v1_xboole_0(k1_xboole_0)),
% 2.27/0.68    inference(cnf_transformation,[],[f3])).
% 2.27/0.68  fof(f3,axiom,(
% 2.27/0.68    v1_xboole_0(k1_xboole_0)),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.27/0.68  fof(f949,plain,(
% 2.27/0.68    spl7_3),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f947])).
% 2.27/0.68  fof(f947,plain,(
% 2.27/0.68    $false | spl7_3),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f388,f320,f67])).
% 2.27/0.68  fof(f320,plain,(
% 2.27/0.68    ~m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))) | spl7_3),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f202,f173,f73])).
% 2.27/0.68  fof(f73,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f37])).
% 2.27/0.68  fof(f37,plain,(
% 2.27/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.27/0.68    inference(flattening,[],[f36])).
% 2.27/0.68  fof(f36,plain,(
% 2.27/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.27/0.68    inference(ennf_transformation,[],[f17])).
% 2.27/0.68  fof(f17,axiom,(
% 2.27/0.68    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.27/0.68  fof(f173,plain,(
% 2.27/0.68    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f77,f53,f74])).
% 2.27/0.68  fof(f74,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f39])).
% 2.27/0.68  fof(f39,plain,(
% 2.27/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.27/0.68    inference(flattening,[],[f38])).
% 2.27/0.68  fof(f38,plain,(
% 2.27/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.27/0.68    inference(ennf_transformation,[],[f15])).
% 2.27/0.68  fof(f15,axiom,(
% 2.27/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.27/0.68  fof(f77,plain,(
% 2.27/0.68    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f13])).
% 2.27/0.68  fof(f13,axiom,(
% 2.27/0.68    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.27/0.68  fof(f202,plain,(
% 2.27/0.68    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl7_3),
% 2.27/0.68    inference(avatar_component_clause,[],[f200])).
% 2.27/0.68  fof(f388,plain,(
% 2.27/0.68    ( ! [X0] : (r1_tarski(k1_zfmisc_1(k2_zfmisc_1(X0,sK1)),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f108,f72])).
% 2.27/0.68  fof(f72,plain,(
% 2.27/0.68    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f35])).
% 2.27/0.68  fof(f35,plain,(
% 2.27/0.68    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.27/0.68    inference(ennf_transformation,[],[f12])).
% 2.27/0.68  fof(f12,axiom,(
% 2.27/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 2.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 2.27/0.68  fof(f108,plain,(
% 2.27/0.68    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK2))) )),
% 2.27/0.68    inference(unit_resulting_resolution,[],[f54,f66])).
% 2.27/0.68  fof(f66,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f33])).
% 2.27/0.68  fof(f931,plain,(
% 2.27/0.68    spl7_12 | ~spl7_13),
% 2.27/0.68    inference(avatar_split_clause,[],[f254,f928,f924])).
% 2.27/0.68  fof(f254,plain,(
% 2.27/0.68    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 2.27/0.68    inference(resolution,[],[f172,f61])).
% 2.27/0.68  fof(f211,plain,(
% 2.27/0.68    ~spl7_3 | ~spl7_4 | ~spl7_5),
% 2.27/0.68    inference(avatar_split_clause,[],[f49,f208,f204,f200])).
% 2.27/0.68  fof(f49,plain,(
% 2.27/0.68    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  fof(f144,plain,(
% 2.27/0.68    spl7_1 | ~spl7_2),
% 2.27/0.68    inference(avatar_split_clause,[],[f50,f141,f137])).
% 2.27/0.68  fof(f50,plain,(
% 2.27/0.68    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  % SZS output end Proof for theBenchmark
% 2.27/0.68  % (9778)------------------------------
% 2.27/0.68  % (9778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.68  % (9778)Termination reason: Refutation
% 2.27/0.68  
% 2.27/0.68  % (9778)Memory used [KB]: 7036
% 2.27/0.68  % (9778)Time elapsed: 0.229 s
% 2.27/0.68  % (9778)------------------------------
% 2.27/0.68  % (9778)------------------------------
% 2.27/0.68  % (9773)Success in time 0.315 s
%------------------------------------------------------------------------------
