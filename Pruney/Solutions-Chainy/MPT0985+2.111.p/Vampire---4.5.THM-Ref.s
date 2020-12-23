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
% DateTime   : Thu Dec  3 13:02:17 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  160 (15659 expanded)
%              Number of leaves         :   20 (3782 expanded)
%              Depth                    :   32
%              Number of atoms          :  462 (92074 expanded)
%              Number of equality atoms :  149 (15652 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8997)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f633,plain,(
    $false ),
    inference(subsumption_resolution,[],[f632,f513])).

fof(f513,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f291,f505])).

fof(f505,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f435,f500])).

fof(f500,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f499,f100])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f499,plain,(
    sK3 = k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f498,f434])).

fof(f434,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f433,f118])).

fof(f118,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

% (8991)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

% (9006)Refutation not found, incomplete strategy% (9006)------------------------------
% (9006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9006)Termination reason: Refutation not found, incomplete strategy

% (9006)Memory used [KB]: 10618
% (9006)Time elapsed: 0.148 s
% (9006)------------------------------
% (9006)------------------------------
fof(f19,conjecture,(
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

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f433,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f432,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f432,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f427,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f427,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f61,f412,f418])).

fof(f418,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f359,f397])).

fof(f397,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f396,f251])).

fof(f251,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f89,f58])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f396,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f394,f153])).

fof(f153,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f94,f58])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

% (8997)Refutation not found, incomplete strategy% (8997)------------------------------
% (8997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8997)Termination reason: Refutation not found, incomplete strategy

% (8997)Memory used [KB]: 10746
% (8997)Time elapsed: 0.150 s
% (8997)------------------------------
% (8997)------------------------------
fof(f17,axiom,(
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

fof(f394,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f359,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f221,f354])).

fof(f354,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f349,f87])).

fof(f349,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f348,f218])).

fof(f218,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f189,f212])).

fof(f212,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f208,f60])).

fof(f60,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f208,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f88,f58])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f189,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f188,f118])).

fof(f188,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f187,f56])).

fof(f187,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f348,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f347,f198])).

fof(f198,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f197,f118])).

fof(f197,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f196,f56])).

fof(f196,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f59])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f347,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) ),
    inference(subsumption_resolution,[],[f345,f118])).

fof(f345,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f180,f56])).

fof(f180,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f178,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f178,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f72])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f221,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f200,f212])).

fof(f200,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f190,f198])).

fof(f190,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f69,f189])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f412,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f349,f397])).

fof(f61,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f498,plain,(
    sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f497,f142])).

fof(f142,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f141,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f64,f63])).

% (9013)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

% (8998)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (9008)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (8994)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f64,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f140,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f497,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f441,f100])).

fof(f441,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f137,f434])).

fof(f137,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f78,f112])).

fof(f112,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f82,f58])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f435,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f231,f434])).

fof(f231,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f228,f118])).

fof(f228,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f67,f212])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f291,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f290,f101])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f290,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f289,f101])).

fof(f289,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0))
      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f287,f151])).

fof(f151,plain,(
    ! [X0,X1] : sP0(X0,k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f94,f107])).

fof(f287,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0))
      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X0),X0) ) ),
    inference(superposition,[],[f102,f249])).

fof(f249,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f89,f107])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

% (9003)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (9001)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f632,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f631,f618])).

fof(f618,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f617,f100])).

fof(f617,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f616,f505])).

fof(f616,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f615,f500])).

fof(f615,plain,(
    k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f614,f142])).

fof(f614,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f613,f101])).

fof(f613,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f479,f500])).

fof(f479,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f372,f434])).

fof(f372,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f355,f78])).

fof(f355,plain,(
    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) ),
    inference(resolution,[],[f349,f82])).

fof(f631,plain,(
    ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f624,f501])).

fof(f501,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f56,f500])).

fof(f624,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f599,f618])).

fof(f599,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f522,f598])).

fof(f598,plain,(
    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f597,f500])).

fof(f597,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f472,f101])).

fof(f472,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) ),
    inference(backward_demodulation,[],[f349,f434])).

fof(f522,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f521,f500])).

fof(f521,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f511,f500])).

fof(f511,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f495,f500])).

fof(f495,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f494,f434])).

fof(f494,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f439,f101])).

fof(f439,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f61,f434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (9012)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (9004)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (8996)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (9000)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (8995)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (8993)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (8990)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.54  % (8992)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (8989)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (9009)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (9010)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.54  % (9005)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.55  % (9014)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.55  % (9017)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (8999)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  % (9018)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.55  % (8996)Refutation found. Thanks to Tanya!
% 1.46/0.55  % SZS status Theorem for theBenchmark
% 1.46/0.55  % (9006)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.55  % (9016)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  % (8997)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.55  fof(f633,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(subsumption_resolution,[],[f632,f513])).
% 1.46/0.55  fof(f513,plain,(
% 1.46/0.55    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f291,f505])).
% 1.46/0.55  fof(f505,plain,(
% 1.46/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.55    inference(backward_demodulation,[],[f435,f500])).
% 1.46/0.55  fof(f500,plain,(
% 1.46/0.55    k1_xboole_0 = sK3),
% 1.46/0.55    inference(forward_demodulation,[],[f499,f100])).
% 1.46/0.55  fof(f100,plain,(
% 1.46/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.46/0.55    inference(equality_resolution,[],[f86])).
% 1.46/0.55  fof(f86,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.46/0.55    inference(cnf_transformation,[],[f52])).
% 1.46/0.55  fof(f52,plain,(
% 1.46/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.46/0.55    inference(flattening,[],[f51])).
% 1.46/0.55  fof(f51,plain,(
% 1.46/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.46/0.55    inference(nnf_transformation,[],[f4])).
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.46/0.55  fof(f499,plain,(
% 1.46/0.55    sK3 = k2_zfmisc_1(sK1,k1_xboole_0)),
% 1.46/0.55    inference(forward_demodulation,[],[f498,f434])).
% 1.46/0.55  fof(f434,plain,(
% 1.46/0.55    k1_xboole_0 = sK2),
% 1.46/0.55    inference(subsumption_resolution,[],[f433,f118])).
% 1.46/0.55  fof(f118,plain,(
% 1.46/0.55    v1_relat_1(sK3)),
% 1.46/0.55    inference(resolution,[],[f87,f58])).
% 1.46/0.55  fof(f58,plain,(
% 1.46/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.46/0.55    inference(cnf_transformation,[],[f42])).
% 1.46/0.55  fof(f42,plain,(
% 1.46/0.55    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f41])).
% 1.46/0.55  fof(f41,plain,(
% 1.46/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.46/0.55    inference(flattening,[],[f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.46/0.55    inference(ennf_transformation,[],[f20])).
% 1.46/0.55  % (8991)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.55  fof(f20,negated_conjecture,(
% 1.46/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.46/0.55    inference(negated_conjecture,[],[f19])).
% 1.46/0.55  % (9006)Refutation not found, incomplete strategy% (9006)------------------------------
% 1.46/0.55  % (9006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (9006)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (9006)Memory used [KB]: 10618
% 1.46/0.55  % (9006)Time elapsed: 0.148 s
% 1.46/0.55  % (9006)------------------------------
% 1.46/0.55  % (9006)------------------------------
% 1.46/0.55  fof(f19,conjecture,(
% 1.46/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.46/0.55  fof(f87,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f33])).
% 1.46/0.55  fof(f33,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(ennf_transformation,[],[f14])).
% 1.46/0.55  fof(f14,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.46/0.55  fof(f433,plain,(
% 1.46/0.55    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 1.46/0.55    inference(subsumption_resolution,[],[f432,f56])).
% 1.46/0.55  fof(f56,plain,(
% 1.46/0.55    v1_funct_1(sK3)),
% 1.46/0.55    inference(cnf_transformation,[],[f42])).
% 1.46/0.55  fof(f432,plain,(
% 1.46/0.55    k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.46/0.55    inference(resolution,[],[f427,f72])).
% 1.46/0.55  fof(f72,plain,(
% 1.46/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f28])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.55    inference(flattening,[],[f27])).
% 1.46/0.55  fof(f27,plain,(
% 1.46/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f12])).
% 1.46/0.55  fof(f12,axiom,(
% 1.46/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.46/0.55  fof(f427,plain,(
% 1.46/0.55    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 1.46/0.55    inference(global_subsumption,[],[f61,f412,f418])).
% 1.46/0.55  fof(f418,plain,(
% 1.46/0.55    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 1.46/0.55    inference(superposition,[],[f359,f397])).
% 1.46/0.55  fof(f397,plain,(
% 1.46/0.55    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.46/0.55    inference(superposition,[],[f396,f251])).
% 1.46/0.55  fof(f251,plain,(
% 1.46/0.55    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.46/0.55    inference(resolution,[],[f89,f58])).
% 1.46/0.55  fof(f89,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f35])).
% 1.46/0.55  fof(f35,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(ennf_transformation,[],[f15])).
% 1.46/0.55  fof(f15,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.46/0.55  fof(f396,plain,(
% 1.46/0.55    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.46/0.55    inference(subsumption_resolution,[],[f394,f153])).
% 1.46/0.55  fof(f153,plain,(
% 1.46/0.55    sP0(sK1,sK3,sK2)),
% 1.46/0.55    inference(resolution,[],[f94,f58])).
% 1.46/0.55  fof(f94,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f55])).
% 1.46/0.55  fof(f55,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(nnf_transformation,[],[f40])).
% 1.46/0.55  fof(f40,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(definition_folding,[],[f37,f39])).
% 1.46/0.55  fof(f39,plain,(
% 1.46/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.46/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f17])).
% 1.46/0.56  % (8997)Refutation not found, incomplete strategy% (8997)------------------------------
% 1.46/0.56  % (8997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8997)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8997)Memory used [KB]: 10746
% 1.46/0.56  % (8997)Time elapsed: 0.150 s
% 1.46/0.56  % (8997)------------------------------
% 1.46/0.56  % (8997)------------------------------
% 1.46/0.56  fof(f17,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.46/0.56  fof(f394,plain,(
% 1.46/0.56    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~sP0(sK1,sK3,sK2)),
% 1.46/0.56    inference(resolution,[],[f90,f57])).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    v1_funct_2(sK3,sK1,sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f90,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.46/0.56    inference(rectify,[],[f53])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f39])).
% 1.46/0.56  fof(f359,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(subsumption_resolution,[],[f221,f354])).
% 1.46/0.56  fof(f354,plain,(
% 1.46/0.56    v1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(resolution,[],[f349,f87])).
% 1.46/0.56  fof(f349,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 1.46/0.56    inference(forward_demodulation,[],[f348,f218])).
% 1.46/0.56  fof(f218,plain,(
% 1.46/0.56    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(backward_demodulation,[],[f189,f212])).
% 1.46/0.56  fof(f212,plain,(
% 1.46/0.56    sK2 = k2_relat_1(sK3)),
% 1.46/0.56    inference(forward_demodulation,[],[f208,f60])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f208,plain,(
% 1.46/0.56    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.46/0.56    inference(resolution,[],[f88,f58])).
% 1.46/0.56  fof(f88,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.46/0.56  fof(f189,plain,(
% 1.46/0.56    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(subsumption_resolution,[],[f188,f118])).
% 1.46/0.56  fof(f188,plain,(
% 1.46/0.56    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.46/0.56    inference(subsumption_resolution,[],[f187,f56])).
% 1.46/0.56  fof(f187,plain,(
% 1.46/0.56    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.46/0.56    inference(resolution,[],[f73,f59])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    v2_funct_1(sK3)),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.46/0.56  fof(f348,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))))),
% 1.46/0.56    inference(forward_demodulation,[],[f347,f198])).
% 1.46/0.56  fof(f198,plain,(
% 1.46/0.56    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(subsumption_resolution,[],[f197,f118])).
% 1.46/0.56  fof(f197,plain,(
% 1.46/0.56    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.46/0.56    inference(subsumption_resolution,[],[f196,f56])).
% 1.46/0.56  fof(f196,plain,(
% 1.46/0.56    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.46/0.56    inference(resolution,[],[f74,f59])).
% 1.46/0.56  fof(f74,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f30])).
% 1.46/0.56  fof(f347,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))),
% 1.46/0.56    inference(subsumption_resolution,[],[f345,f118])).
% 1.46/0.56  fof(f345,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~v1_relat_1(sK3)),
% 1.46/0.56    inference(resolution,[],[f180,f56])).
% 1.46/0.56  fof(f180,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f178,f71])).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f28])).
% 1.46/0.56  fof(f178,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(resolution,[],[f70,f72])).
% 1.46/0.56  fof(f70,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.46/0.56  fof(f221,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(backward_demodulation,[],[f200,f212])).
% 1.46/0.56  fof(f200,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(backward_demodulation,[],[f190,f198])).
% 1.46/0.56  fof(f190,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(superposition,[],[f69,f189])).
% 1.46/0.56  fof(f69,plain,(
% 1.46/0.56    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f412,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k1_xboole_0 = sK2),
% 1.46/0.56    inference(superposition,[],[f349,f397])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f498,plain,(
% 1.46/0.56    sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f497,f142])).
% 1.46/0.56  fof(f142,plain,(
% 1.46/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.56    inference(resolution,[],[f141,f107])).
% 1.46/0.56  fof(f107,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.46/0.56    inference(forward_demodulation,[],[f64,f63])).
% 1.46/0.56  % (9013)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.46/0.56  % (8998)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.56  % (9008)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.56  % (8994)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.46/0.56  fof(f141,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(resolution,[],[f140,f80])).
% 1.46/0.56  fof(f80,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f49])).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(rectify,[],[f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(nnf_transformation,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.56  fof(f140,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.46/0.56    inference(resolution,[],[f97,f62])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    inference(cnf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.46/0.56  fof(f97,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.46/0.56  fof(f497,plain,(
% 1.46/0.56    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.46/0.56    inference(forward_demodulation,[],[f441,f100])).
% 1.46/0.56  fof(f441,plain,(
% 1.46/0.56    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.46/0.56    inference(backward_demodulation,[],[f137,f434])).
% 1.46/0.56  fof(f137,plain,(
% 1.46/0.56    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.46/0.56    inference(resolution,[],[f78,f112])).
% 1.46/0.56  fof(f112,plain,(
% 1.46/0.56    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 1.46/0.56    inference(resolution,[],[f82,f58])).
% 1.46/0.56  fof(f82,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.46/0.56    inference(nnf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.56  fof(f78,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f45])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(flattening,[],[f44])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.56  fof(f435,plain,(
% 1.46/0.56    k1_xboole_0 = k1_relat_1(sK3)),
% 1.46/0.56    inference(subsumption_resolution,[],[f231,f434])).
% 1.46/0.56  fof(f231,plain,(
% 1.46/0.56    k1_xboole_0 != sK2 | k1_xboole_0 = k1_relat_1(sK3)),
% 1.46/0.56    inference(subsumption_resolution,[],[f228,f118])).
% 1.46/0.56  fof(f228,plain,(
% 1.46/0.56    k1_xboole_0 != sK2 | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.46/0.56    inference(superposition,[],[f67,f212])).
% 1.46/0.56  fof(f67,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.46/0.56  fof(f291,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.46/0.56    inference(forward_demodulation,[],[f290,f101])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.46/0.56    inference(equality_resolution,[],[f85])).
% 1.46/0.56  fof(f85,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f52])).
% 1.46/0.56  fof(f290,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0)) )),
% 1.46/0.56    inference(forward_demodulation,[],[f289,f101])).
% 1.46/0.56  fof(f289,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f287,f151])).
% 1.46/0.56  fof(f151,plain,(
% 1.46/0.56    ( ! [X0,X1] : (sP0(X0,k2_zfmisc_1(X0,X1),X1)) )),
% 1.46/0.56    inference(resolution,[],[f94,f107])).
% 1.46/0.56  fof(f287,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) | ~sP0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X0),X0)) )),
% 1.46/0.56    inference(superposition,[],[f102,f249])).
% 1.46/0.56  fof(f249,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 1.46/0.56    inference(resolution,[],[f89,f107])).
% 1.46/0.56  fof(f102,plain,(
% 1.46/0.56    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 1.46/0.56    inference(equality_resolution,[],[f93])).
% 1.46/0.56  fof(f93,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f54])).
% 1.46/0.56  % (9003)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.56  % (9001)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.56  fof(f632,plain,(
% 1.46/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 1.46/0.56    inference(forward_demodulation,[],[f631,f618])).
% 1.46/0.56  fof(f618,plain,(
% 1.46/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.46/0.56    inference(forward_demodulation,[],[f617,f100])).
% 1.46/0.56  fof(f617,plain,(
% 1.46/0.56    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_xboole_0)),
% 1.46/0.56    inference(forward_demodulation,[],[f616,f505])).
% 1.46/0.56  fof(f616,plain,(
% 1.46/0.56    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0))),
% 1.46/0.56    inference(forward_demodulation,[],[f615,f500])).
% 1.46/0.56  fof(f615,plain,(
% 1.46/0.56    k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.46/0.56    inference(subsumption_resolution,[],[f614,f142])).
% 1.46/0.56  fof(f614,plain,(
% 1.46/0.56    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.46/0.56    inference(forward_demodulation,[],[f613,f101])).
% 1.46/0.56  fof(f613,plain,(
% 1.46/0.56    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.46/0.56    inference(forward_demodulation,[],[f479,f500])).
% 1.46/0.56  fof(f479,plain,(
% 1.46/0.56    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.46/0.56    inference(backward_demodulation,[],[f372,f434])).
% 1.46/0.56  fof(f372,plain,(
% 1.46/0.56    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.46/0.56    inference(resolution,[],[f355,f78])).
% 1.46/0.56  fof(f355,plain,(
% 1.46/0.56    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))),
% 1.46/0.56    inference(resolution,[],[f349,f82])).
% 1.46/0.56  fof(f631,plain,(
% 1.46/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 1.46/0.56    inference(subsumption_resolution,[],[f624,f501])).
% 1.46/0.56  fof(f501,plain,(
% 1.46/0.56    v1_funct_1(k1_xboole_0)),
% 1.46/0.56    inference(backward_demodulation,[],[f56,f500])).
% 1.46/0.56  fof(f624,plain,(
% 1.46/0.56    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 1.46/0.56    inference(backward_demodulation,[],[f599,f618])).
% 1.46/0.56  fof(f599,plain,(
% 1.46/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.46/0.56    inference(subsumption_resolution,[],[f522,f598])).
% 1.46/0.56  fof(f598,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.56    inference(forward_demodulation,[],[f597,f500])).
% 1.46/0.56  fof(f597,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.56    inference(forward_demodulation,[],[f472,f101])).
% 1.46/0.56  fof(f472,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3))))),
% 1.46/0.56    inference(backward_demodulation,[],[f349,f434])).
% 1.46/0.56  fof(f522,plain,(
% 1.46/0.56    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.46/0.56    inference(forward_demodulation,[],[f521,f500])).
% 1.46/0.56  fof(f521,plain,(
% 1.46/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.56    inference(forward_demodulation,[],[f511,f500])).
% 1.46/0.56  fof(f511,plain,(
% 1.46/0.56    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.56    inference(backward_demodulation,[],[f495,f500])).
% 1.46/0.56  fof(f495,plain,(
% 1.46/0.56    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(forward_demodulation,[],[f494,f434])).
% 1.46/0.56  fof(f494,plain,(
% 1.46/0.56    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(forward_demodulation,[],[f439,f101])).
% 1.46/0.56  fof(f439,plain,(
% 1.46/0.56    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.46/0.56    inference(backward_demodulation,[],[f61,f434])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (8996)------------------------------
% 1.46/0.56  % (8996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8996)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (8996)Memory used [KB]: 6652
% 1.46/0.56  % (8996)Time elapsed: 0.105 s
% 1.46/0.56  % (8996)------------------------------
% 1.46/0.56  % (8996)------------------------------
% 1.46/0.56  % (8988)Success in time 0.199 s
%------------------------------------------------------------------------------
