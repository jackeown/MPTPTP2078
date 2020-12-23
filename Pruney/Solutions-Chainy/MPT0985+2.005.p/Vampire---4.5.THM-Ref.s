%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:59 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  176 (1656 expanded)
%              Number of leaves         :   28 ( 417 expanded)
%              Depth                    :   21
%              Number of atoms          :  470 (5795 expanded)
%              Number of equality atoms :   81 ( 774 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1891,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f186,f222,f277,f284,f347,f423,f840,f854,f858,f1861])).

fof(f1861,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f1856])).

fof(f1856,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f1499,f1741,f1440,f1502,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f1502,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1442,f95])).

fof(f95,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1442,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f393,f1403])).

fof(f1403,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f1369,f370])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | sK2 = X0 )
    | ~ spl4_5 ),
    inference(resolution,[],[f350,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f350,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f221,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f221,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_5
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1369,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f1364,f90])).

fof(f1364,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f99,f991,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f991,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f990,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

% (26612)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f990,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f886,f96])).

fof(f96,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f886,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f465,f272])).

fof(f272,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f465,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f452,f453,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f453,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f447,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f447,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f438,f125])).

fof(f125,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f119,f63])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
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

fof(f119,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f61,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f438,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f399,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f399,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f99,f369,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f369,plain,
    ( ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f350,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f452,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f447,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f99,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f393,plain,
    ( ! [X0,X1] : k1_relat_1(sK2) = k1_relset_1(X0,X1,sK2)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f369,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1440,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f369,f1403])).

fof(f1741,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f1456,f1704])).

fof(f1704,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f1369,f1694,f94])).

fof(f1694,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f1011,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1011,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1010,f103])).

fof(f1010,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f900,f95])).

fof(f900,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f502,f272])).

fof(f502,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),k1_relat_1(sK1))))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f501,f467])).

fof(f467,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f453,f452,f463,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f463,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f447,f452,f453,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

% (26634)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f40,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f501,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k1_relat_1(sK1))))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f499,f468])).

fof(f468,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f453,f452,f463,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f499,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1)))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f461,f462,f83])).

fof(f462,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f452,f453,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f461,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f452,f453,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1456,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f871,f1403])).

fof(f871,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f181,f272])).

fof(f181,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1499,plain,
    ( k1_xboole_0 != sK0
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(forward_demodulation,[],[f1437,f95])).

fof(f1437,plain,
    ( k1_relat_1(k1_xboole_0) != sK0
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(backward_demodulation,[],[f275,f1403])).

fof(f275,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl4_10
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f858,plain,
    ( spl4_2
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | spl4_2
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f431,f181])).

fof(f431,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f158,f276])).

fof(f276,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f158,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f157,f143])).

fof(f143,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f132,f125])).

fof(f132,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f59,f62,f118,f65])).

fof(f118,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f61,f71])).

% (26631)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f157,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f152,f133])).

fof(f133,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f59,f62,f118,f66])).

fof(f152,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f134,f135,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f135,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f59,f118,f68])).

fof(f134,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f59,f118,f67])).

fof(f854,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f118,f59,f185,f68])).

fof(f185,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_3
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f840,plain,
    ( spl4_1
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | spl4_1
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f202,f430,f88])).

fof(f430,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f156,f276])).

% (26636)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f156,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f155,f143])).

fof(f155,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f153,f133])).

fof(f153,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(unit_resulting_resolution,[],[f134,f135,f83])).

fof(f202,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f177,f87])).

fof(f177,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_1
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f423,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f325,f319,f88])).

fof(f319,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f296,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f296,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f156,f272])).

fof(f325,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k1_xboole_0)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f301,f104])).

fof(f301,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl4_1
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f202,f272])).

fof(f347,plain,
    ( spl4_4
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl4_4
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f99,f330])).

fof(f330,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f305,f103])).

fof(f305,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl4_4
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f218,f272])).

fof(f218,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_4
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f284,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f120,f268,f87])).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f120,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f61,f88])).

fof(f277,plain,
    ( ~ spl4_8
    | spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f128,f274,f270,f266])).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f116,f117])).

fof(f117,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f61,f100])).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f60,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f222,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f123,f220,f216])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f61,f102])).

fof(f186,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f183,f179,f175])).

fof(f58,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:23:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (26625)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (26615)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (26618)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.53  % (26616)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (26614)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.54  % (26635)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.54  % (26611)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (26613)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.55  % (26628)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.55  % (26639)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.55  % (26632)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.55  % (26640)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.55  % (26617)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.56  % (26627)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.56  % (26633)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.56  % (26641)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.56  % (26638)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.56  % (26619)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.56  % (26615)Refutation found. Thanks to Tanya!
% 1.33/0.56  % SZS status Theorem for theBenchmark
% 1.33/0.56  % SZS output start Proof for theBenchmark
% 1.33/0.56  fof(f1891,plain,(
% 1.33/0.56    $false),
% 1.33/0.56    inference(avatar_sat_refutation,[],[f186,f222,f277,f284,f347,f423,f840,f854,f858,f1861])).
% 1.33/0.56  fof(f1861,plain,(
% 1.33/0.56    spl4_2 | ~spl4_5 | ~spl4_9 | spl4_10),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f1856])).
% 1.33/0.56  fof(f1856,plain,(
% 1.33/0.56    $false | (spl4_2 | ~spl4_5 | ~spl4_9 | spl4_10)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f1499,f1741,f1440,f1502,f80])).
% 1.33/0.56  fof(f80,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f45])).
% 1.33/0.56  fof(f45,plain,(
% 1.33/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.56    inference(flattening,[],[f44])).
% 1.33/0.56  fof(f44,plain,(
% 1.33/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.56    inference(ennf_transformation,[],[f27])).
% 1.33/0.56  fof(f27,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.33/0.56  fof(f1502,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f1442,f95])).
% 1.33/0.56  fof(f95,plain,(
% 1.33/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.56    inference(cnf_transformation,[],[f16])).
% 1.33/0.56  fof(f16,axiom,(
% 1.33/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.33/0.56  fof(f1442,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f393,f1403])).
% 1.33/0.56  fof(f1403,plain,(
% 1.33/0.56    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f1369,f370])).
% 1.33/0.56  fof(f370,plain,(
% 1.33/0.56    ( ! [X0] : (~r1_tarski(X0,sK2) | sK2 = X0) ) | ~spl4_5),
% 1.33/0.56    inference(resolution,[],[f350,f94])).
% 1.33/0.56  fof(f94,plain,(
% 1.33/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.33/0.56    inference(cnf_transformation,[],[f3])).
% 1.33/0.56  fof(f3,axiom,(
% 1.33/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.56  fof(f350,plain,(
% 1.33/0.56    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f221,f90])).
% 1.33/0.56  fof(f90,plain,(
% 1.33/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f51])).
% 1.33/0.56  fof(f51,plain,(
% 1.33/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.56    inference(ennf_transformation,[],[f1])).
% 1.33/0.56  fof(f1,axiom,(
% 1.33/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.56  fof(f221,plain,(
% 1.33/0.56    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl4_5),
% 1.33/0.56    inference(avatar_component_clause,[],[f220])).
% 1.33/0.56  fof(f220,plain,(
% 1.33/0.56    spl4_5 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.33/0.56  fof(f1369,plain,(
% 1.33/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f1364,f90])).
% 1.33/0.56  fof(f1364,plain,(
% 1.33/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f99,f991,f102])).
% 1.33/0.56  fof(f102,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f57])).
% 1.33/0.56  fof(f57,plain,(
% 1.33/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.33/0.56    inference(ennf_transformation,[],[f9])).
% 1.33/0.56  fof(f9,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.33/0.56  fof(f991,plain,(
% 1.33/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f990,f103])).
% 1.33/0.56  fof(f103,plain,(
% 1.33/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.33/0.56    inference(equality_resolution,[],[f75])).
% 1.33/0.56  fof(f75,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f4])).
% 1.33/0.56  fof(f4,axiom,(
% 1.33/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.33/0.56  % (26612)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.56  fof(f990,plain,(
% 1.33/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f886,f96])).
% 1.33/0.56  fof(f96,plain,(
% 1.33/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.33/0.56    inference(cnf_transformation,[],[f16])).
% 1.33/0.56  fof(f886,plain,(
% 1.33/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f465,f272])).
% 1.33/0.56  fof(f272,plain,(
% 1.33/0.56    k1_xboole_0 = sK1 | ~spl4_9),
% 1.33/0.56    inference(avatar_component_clause,[],[f270])).
% 1.33/0.56  fof(f270,plain,(
% 1.33/0.56    spl4_9 <=> k1_xboole_0 = sK1),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.33/0.56  fof(f465,plain,(
% 1.33/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f452,f453,f83])).
% 1.33/0.56  fof(f83,plain,(
% 1.33/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f47])).
% 1.33/0.56  fof(f47,plain,(
% 1.33/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.56    inference(flattening,[],[f46])).
% 1.33/0.56  fof(f46,plain,(
% 1.33/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.56    inference(ennf_transformation,[],[f28])).
% 1.33/0.56  fof(f28,axiom,(
% 1.33/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.33/0.56  fof(f453,plain,(
% 1.33/0.56    v1_funct_1(sK1) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f447,f84])).
% 1.33/0.56  fof(f84,plain,(
% 1.33/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f48])).
% 1.33/0.56  fof(f48,plain,(
% 1.33/0.56    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f17])).
% 1.33/0.56  fof(f17,axiom,(
% 1.33/0.56    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.33/0.56  fof(f447,plain,(
% 1.33/0.56    v1_xboole_0(sK1) | ~spl4_5),
% 1.33/0.56    inference(forward_demodulation,[],[f438,f125])).
% 1.33/0.56  fof(f125,plain,(
% 1.33/0.56    sK1 = k2_relat_1(sK2)),
% 1.33/0.56    inference(forward_demodulation,[],[f119,f63])).
% 1.33/0.56  fof(f63,plain,(
% 1.33/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.33/0.56    inference(cnf_transformation,[],[f32])).
% 1.33/0.56  fof(f32,plain,(
% 1.33/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.33/0.56    inference(flattening,[],[f31])).
% 1.33/0.56  fof(f31,plain,(
% 1.33/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.33/0.56    inference(ennf_transformation,[],[f30])).
% 1.33/0.56  fof(f30,negated_conjecture,(
% 1.33/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.33/0.56    inference(negated_conjecture,[],[f29])).
% 1.33/0.56  fof(f29,conjecture,(
% 1.33/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.33/0.56  fof(f119,plain,(
% 1.33/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f61,f69])).
% 1.33/0.56  fof(f69,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f39])).
% 1.33/0.56  fof(f39,plain,(
% 1.33/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.56    inference(ennf_transformation,[],[f26])).
% 1.33/0.56  fof(f26,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.56  fof(f61,plain,(
% 1.33/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.56    inference(cnf_transformation,[],[f32])).
% 1.33/0.56  fof(f438,plain,(
% 1.33/0.56    v1_xboole_0(k2_relat_1(sK2)) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f399,f98])).
% 1.33/0.56  fof(f98,plain,(
% 1.33/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f53])).
% 1.33/0.56  fof(f53,plain,(
% 1.33/0.56    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f11])).
% 1.33/0.56  fof(f11,axiom,(
% 1.33/0.56    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 1.33/0.56  fof(f399,plain,(
% 1.33/0.56    v1_xboole_0(sK2) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f99,f369,f72])).
% 1.33/0.56  fof(f72,plain,(
% 1.33/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f43])).
% 1.33/0.56  fof(f43,plain,(
% 1.33/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f7])).
% 1.33/0.56  fof(f7,axiom,(
% 1.33/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.33/0.56  fof(f369,plain,(
% 1.33/0.56    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f350,f87])).
% 1.33/0.56  fof(f87,plain,(
% 1.33/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f8])).
% 1.33/0.56  fof(f8,axiom,(
% 1.33/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.33/0.56  fof(f452,plain,(
% 1.33/0.56    v1_relat_1(sK1) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f447,f97])).
% 1.33/0.56  fof(f97,plain,(
% 1.33/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f52])).
% 1.33/0.56  fof(f52,plain,(
% 1.33/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f10])).
% 1.33/0.56  fof(f10,axiom,(
% 1.33/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.33/0.56  fof(f99,plain,(
% 1.33/0.56    v1_xboole_0(k1_xboole_0)),
% 1.33/0.56    inference(cnf_transformation,[],[f2])).
% 1.33/0.56  fof(f2,axiom,(
% 1.33/0.56    v1_xboole_0(k1_xboole_0)),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.33/0.56  fof(f393,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k1_relat_1(sK2) = k1_relset_1(X0,X1,sK2)) ) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f369,f100])).
% 1.33/0.56  fof(f100,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f54])).
% 1.33/0.56  fof(f54,plain,(
% 1.33/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.56    inference(ennf_transformation,[],[f25])).
% 1.33/0.56  fof(f25,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.33/0.56  fof(f1440,plain,(
% 1.33/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f369,f1403])).
% 1.33/0.56  fof(f1741,plain,(
% 1.33/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl4_2 | ~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f1456,f1704])).
% 1.33/0.56  fof(f1704,plain,(
% 1.33/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f1369,f1694,f94])).
% 1.33/0.56  fof(f1694,plain,(
% 1.33/0.56    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f1011,f88])).
% 1.33/0.56  fof(f88,plain,(
% 1.33/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f8])).
% 1.33/0.56  fof(f1011,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f1010,f103])).
% 1.33/0.56  fof(f1010,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f900,f95])).
% 1.33/0.56  fof(f900,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))) | (~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f502,f272])).
% 1.33/0.56  fof(f502,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),k1_relat_1(sK1)))) | ~spl4_5),
% 1.33/0.56    inference(forward_demodulation,[],[f501,f467])).
% 1.33/0.56  fof(f467,plain,(
% 1.33/0.56    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f453,f452,f463,f65])).
% 1.33/0.56  fof(f65,plain,(
% 1.33/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f36])).
% 1.33/0.56  fof(f36,plain,(
% 1.33/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.56    inference(flattening,[],[f35])).
% 1.33/0.56  fof(f35,plain,(
% 1.33/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.56    inference(ennf_transformation,[],[f22])).
% 1.33/0.56  fof(f22,axiom,(
% 1.33/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.33/0.56  fof(f463,plain,(
% 1.33/0.56    v2_funct_1(sK1) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f447,f452,f453,f70])).
% 1.33/0.56  fof(f70,plain,(
% 1.33/0.56    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f41])).
% 1.33/0.56  fof(f41,plain,(
% 1.33/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.33/0.56    inference(flattening,[],[f40])).
% 1.33/0.56  % (26634)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.56  fof(f40,plain,(
% 1.33/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.33/0.56    inference(ennf_transformation,[],[f18])).
% 1.33/0.56  fof(f18,axiom,(
% 1.33/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.33/0.56  fof(f501,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k1_relat_1(sK1)))) | ~spl4_5),
% 1.33/0.56    inference(forward_demodulation,[],[f499,f468])).
% 1.33/0.56  fof(f468,plain,(
% 1.33/0.56    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f453,f452,f463,f66])).
% 1.33/0.56  fof(f66,plain,(
% 1.33/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f36])).
% 1.33/0.56  fof(f499,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1))))) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f461,f462,f83])).
% 1.33/0.56  fof(f462,plain,(
% 1.33/0.56    v1_funct_1(k2_funct_1(sK1)) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f452,f453,f68])).
% 1.33/0.56  fof(f68,plain,(
% 1.33/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f38])).
% 1.33/0.56  fof(f38,plain,(
% 1.33/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.56    inference(flattening,[],[f37])).
% 1.33/0.56  fof(f37,plain,(
% 1.33/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.56    inference(ennf_transformation,[],[f20])).
% 1.33/0.56  fof(f20,axiom,(
% 1.33/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.33/0.56  fof(f461,plain,(
% 1.33/0.56    v1_relat_1(k2_funct_1(sK1)) | ~spl4_5),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f452,f453,f67])).
% 1.33/0.56  fof(f67,plain,(
% 1.33/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f38])).
% 1.33/0.56  fof(f1456,plain,(
% 1.33/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_5 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f871,f1403])).
% 1.33/0.56  fof(f871,plain,(
% 1.33/0.56    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f181,f272])).
% 1.33/0.56  fof(f181,plain,(
% 1.33/0.56    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 1.33/0.56    inference(avatar_component_clause,[],[f179])).
% 1.33/0.56  fof(f179,plain,(
% 1.33/0.56    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.33/0.56  fof(f1499,plain,(
% 1.33/0.56    k1_xboole_0 != sK0 | (~spl4_5 | ~spl4_9 | spl4_10)),
% 1.33/0.56    inference(forward_demodulation,[],[f1437,f95])).
% 1.33/0.56  fof(f1437,plain,(
% 1.33/0.56    k1_relat_1(k1_xboole_0) != sK0 | (~spl4_5 | ~spl4_9 | spl4_10)),
% 1.33/0.56    inference(backward_demodulation,[],[f275,f1403])).
% 1.33/0.56  fof(f275,plain,(
% 1.33/0.56    sK0 != k1_relat_1(sK2) | spl4_10),
% 1.33/0.56    inference(avatar_component_clause,[],[f274])).
% 1.33/0.56  fof(f274,plain,(
% 1.33/0.56    spl4_10 <=> sK0 = k1_relat_1(sK2)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.33/0.56  fof(f858,plain,(
% 1.33/0.56    spl4_2 | ~spl4_10),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f855])).
% 1.33/0.56  fof(f855,plain,(
% 1.33/0.56    $false | (spl4_2 | ~spl4_10)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f431,f181])).
% 1.33/0.56  fof(f431,plain,(
% 1.33/0.56    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl4_10),
% 1.33/0.56    inference(backward_demodulation,[],[f158,f276])).
% 1.33/0.56  fof(f276,plain,(
% 1.33/0.56    sK0 = k1_relat_1(sK2) | ~spl4_10),
% 1.33/0.56    inference(avatar_component_clause,[],[f274])).
% 1.33/0.56  fof(f158,plain,(
% 1.33/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 1.33/0.56    inference(forward_demodulation,[],[f157,f143])).
% 1.33/0.56  fof(f143,plain,(
% 1.33/0.56    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.33/0.56    inference(forward_demodulation,[],[f132,f125])).
% 1.33/0.56  fof(f132,plain,(
% 1.33/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f59,f62,f118,f65])).
% 1.33/0.56  fof(f118,plain,(
% 1.33/0.56    v1_relat_1(sK2)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f61,f71])).
% 1.33/0.56  % (26631)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.56  fof(f71,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f42])).
% 1.33/0.56  fof(f42,plain,(
% 1.33/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.56    inference(ennf_transformation,[],[f23])).
% 1.33/0.56  fof(f23,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.33/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.33/0.56  fof(f62,plain,(
% 1.33/0.56    v2_funct_1(sK2)),
% 1.33/0.56    inference(cnf_transformation,[],[f32])).
% 1.33/0.56  fof(f59,plain,(
% 1.33/0.56    v1_funct_1(sK2)),
% 1.33/0.56    inference(cnf_transformation,[],[f32])).
% 1.33/0.56  fof(f157,plain,(
% 1.33/0.56    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))),
% 1.33/0.56    inference(forward_demodulation,[],[f152,f133])).
% 1.33/0.56  fof(f133,plain,(
% 1.33/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f59,f62,f118,f66])).
% 1.33/0.56  fof(f152,plain,(
% 1.33/0.56    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f134,f135,f82])).
% 1.33/0.56  fof(f82,plain,(
% 1.33/0.56    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f47])).
% 1.33/0.56  fof(f135,plain,(
% 1.33/0.56    v1_funct_1(k2_funct_1(sK2))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f59,f118,f68])).
% 1.33/0.56  fof(f134,plain,(
% 1.33/0.56    v1_relat_1(k2_funct_1(sK2))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f59,f118,f67])).
% 1.33/0.56  fof(f854,plain,(
% 1.33/0.56    spl4_3),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f848])).
% 1.33/0.56  fof(f848,plain,(
% 1.33/0.56    $false | spl4_3),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f118,f59,f185,f68])).
% 1.33/0.56  fof(f185,plain,(
% 1.33/0.56    ~v1_funct_1(k2_funct_1(sK2)) | spl4_3),
% 1.33/0.56    inference(avatar_component_clause,[],[f183])).
% 1.33/0.56  fof(f183,plain,(
% 1.33/0.56    spl4_3 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.33/0.56  fof(f840,plain,(
% 1.33/0.56    spl4_1 | ~spl4_10),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f832])).
% 1.33/0.56  fof(f832,plain,(
% 1.33/0.56    $false | (spl4_1 | ~spl4_10)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f202,f430,f88])).
% 1.33/0.56  fof(f430,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 1.33/0.56    inference(backward_demodulation,[],[f156,f276])).
% 1.33/0.56  % (26636)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.56  fof(f156,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.33/0.56    inference(forward_demodulation,[],[f155,f143])).
% 1.33/0.56  fof(f155,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 1.33/0.56    inference(forward_demodulation,[],[f153,f133])).
% 1.33/0.56  fof(f153,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f134,f135,f83])).
% 1.33/0.56  fof(f202,plain,(
% 1.33/0.56    ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) | spl4_1),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f177,f87])).
% 1.33/0.56  fof(f177,plain,(
% 1.33/0.56    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_1),
% 1.33/0.56    inference(avatar_component_clause,[],[f175])).
% 1.33/0.56  fof(f175,plain,(
% 1.33/0.56    spl4_1 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.33/0.56  fof(f423,plain,(
% 1.33/0.56    spl4_1 | ~spl4_9),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f416])).
% 1.33/0.56  fof(f416,plain,(
% 1.33/0.56    $false | (spl4_1 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f325,f319,f88])).
% 1.33/0.56  fof(f319,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl4_9),
% 1.33/0.56    inference(forward_demodulation,[],[f296,f104])).
% 1.33/0.56  fof(f104,plain,(
% 1.33/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.33/0.56    inference(equality_resolution,[],[f74])).
% 1.33/0.56  fof(f74,plain,(
% 1.33/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f4])).
% 1.33/0.56  fof(f296,plain,(
% 1.33/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | ~spl4_9),
% 1.33/0.56    inference(backward_demodulation,[],[f156,f272])).
% 1.33/0.56  fof(f325,plain,(
% 1.33/0.56    ~r1_tarski(k2_funct_1(sK2),k1_xboole_0) | (spl4_1 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f301,f104])).
% 1.33/0.56  fof(f301,plain,(
% 1.33/0.56    ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,sK0)) | (spl4_1 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f202,f272])).
% 1.33/0.56  fof(f347,plain,(
% 1.33/0.56    spl4_4 | ~spl4_9),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f343])).
% 1.33/0.56  fof(f343,plain,(
% 1.33/0.56    $false | (spl4_4 | ~spl4_9)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f99,f330])).
% 1.33/0.56  fof(f330,plain,(
% 1.33/0.56    ~v1_xboole_0(k1_xboole_0) | (spl4_4 | ~spl4_9)),
% 1.33/0.56    inference(forward_demodulation,[],[f305,f103])).
% 1.33/0.56  fof(f305,plain,(
% 1.33/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl4_4 | ~spl4_9)),
% 1.33/0.56    inference(backward_demodulation,[],[f218,f272])).
% 1.33/0.56  fof(f218,plain,(
% 1.33/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.33/0.56    inference(avatar_component_clause,[],[f216])).
% 1.33/0.56  fof(f216,plain,(
% 1.33/0.56    spl4_4 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.33/0.56  fof(f284,plain,(
% 1.33/0.56    spl4_8),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f280])).
% 1.33/0.56  fof(f280,plain,(
% 1.33/0.56    $false | spl4_8),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f120,f268,f87])).
% 1.33/0.56  fof(f268,plain,(
% 1.33/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_8),
% 1.33/0.56    inference(avatar_component_clause,[],[f266])).
% 1.33/0.56  fof(f266,plain,(
% 1.33/0.56    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.33/0.56  fof(f120,plain,(
% 1.33/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f61,f88])).
% 1.33/0.56  fof(f277,plain,(
% 1.33/0.56    ~spl4_8 | spl4_9 | spl4_10),
% 1.33/0.56    inference(avatar_split_clause,[],[f128,f274,f270,f266])).
% 1.33/0.56  fof(f128,plain,(
% 1.33/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.56    inference(backward_demodulation,[],[f116,f117])).
% 1.33/0.56  fof(f117,plain,(
% 1.33/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f61,f100])).
% 1.33/0.56  fof(f116,plain,(
% 1.33/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.56    inference(resolution,[],[f60,f81])).
% 1.33/0.56  fof(f81,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.56    inference(cnf_transformation,[],[f45])).
% 1.33/0.56  fof(f60,plain,(
% 1.33/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.33/0.56    inference(cnf_transformation,[],[f32])).
% 1.33/0.56  fof(f222,plain,(
% 1.33/0.56    ~spl4_4 | spl4_5),
% 1.33/0.56    inference(avatar_split_clause,[],[f123,f220,f216])).
% 1.33/0.56  fof(f123,plain,(
% 1.33/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 1.33/0.56    inference(resolution,[],[f61,f102])).
% 1.33/0.56  fof(f186,plain,(
% 1.33/0.56    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.33/0.56    inference(avatar_split_clause,[],[f58,f183,f179,f175])).
% 1.33/0.56  fof(f58,plain,(
% 1.33/0.56    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.33/0.56    inference(cnf_transformation,[],[f32])).
% 1.33/0.56  % SZS output end Proof for theBenchmark
% 1.33/0.56  % (26615)------------------------------
% 1.33/0.56  % (26615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (26615)Termination reason: Refutation
% 1.33/0.56  
% 1.33/0.56  % (26615)Memory used [KB]: 6908
% 1.33/0.56  % (26615)Time elapsed: 0.134 s
% 1.33/0.56  % (26615)------------------------------
% 1.33/0.56  % (26615)------------------------------
% 1.33/0.56  % (26631)Refutation not found, incomplete strategy% (26631)------------------------------
% 1.33/0.56  % (26631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (26631)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (26631)Memory used [KB]: 10618
% 1.33/0.56  % (26631)Time elapsed: 0.147 s
% 1.33/0.56  % (26631)------------------------------
% 1.33/0.56  % (26631)------------------------------
% 1.50/0.57  % (26605)Success in time 0.19 s
%------------------------------------------------------------------------------
