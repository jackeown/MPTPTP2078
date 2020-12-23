%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:54 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  141 (1990 expanded)
%              Number of leaves         :   20 ( 411 expanded)
%              Depth                    :   17
%              Number of atoms          :  415 (8887 expanded)
%              Number of equality atoms :   96 ( 392 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f211,f242,f258,f649])).

fof(f649,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f301,f561])).

fof(f561,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f553,f528])).

fof(f528,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f369,f503])).

fof(f503,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f324,f367,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f367,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f291,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f291,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f207,f259])).

fof(f259,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f154,f240])).

fof(f240,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl2_5
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f154,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f118,f116,f120,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f120,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f49,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f116,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f48,f49,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f48,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f49,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f207,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f179,f177,f181,f76])).

fof(f181,plain,(
    v5_relat_1(k2_funct_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f136,f83])).

fof(f136,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f126,f122])).

fof(f122,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f177,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f133,f135,f136,f61])).

fof(f135,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(backward_demodulation,[],[f125,f122])).

fof(f125,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f133,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f123,f122])).

fof(f123,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f48,f47,f49,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f179,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f136,f81])).

fof(f324,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f179,f232])).

fof(f369,plain,
    ( k1_xboole_0 = k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f296,f232])).

fof(f296,plain,
    ( k1_xboole_0 = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f276,f91])).

fof(f91,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f72,f52])).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f276,plain,
    ( k6_partfun1(k1_xboole_0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f155,f259])).

fof(f155,plain,(
    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f141,f154])).

fof(f141,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f115,f118,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f52])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f115,plain,(
    v2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f46,f48,f49,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f553,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f373,f506])).

fof(f506,plain,
    ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f314,f503])).

fof(f314,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f140,f232])).

fof(f140,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f115,f118,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f52])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f373,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f300,f232])).

fof(f300,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0)
    | spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f293,f91])).

fof(f293,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0))
    | spl2_2
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f212,f259])).

fof(f212,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | spl2_2 ),
    inference(forward_demodulation,[],[f152,f199])).

fof(f199,plain,(
    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f174,f140])).

fof(f174,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f133,f136,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f152,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl2_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f301,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f294,f91])).

fof(f294,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f213,f259])).

fof(f213,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f147,f200])).

fof(f200,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f172,f155])).

fof(f172,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f46,f133,f49,f136,f53])).

fof(f147,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f258,plain,
    ( spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl2_2
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f86,f249,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f249,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl2_2
    | spl2_5 ),
    inference(backward_demodulation,[],[f212,f248])).

fof(f248,plain,
    ( sK0 = k1_relat_1(sK1)
    | spl2_5 ),
    inference(backward_demodulation,[],[f117,f244])).

fof(f244,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f47,f49,f243,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f243,plain,
    ( k1_xboole_0 != sK0
    | spl2_5 ),
    inference(superposition,[],[f241,f154])).

fof(f241,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f239])).

fof(f117,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f49,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f59,f52])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f242,plain,
    ( spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f143,f239,f230])).

fof(f143,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f118,f79])).

fof(f211,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f86,f201,f101])).

fof(f201,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl2_1 ),
    inference(backward_demodulation,[],[f148,f200])).

fof(f148,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f153,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f138,f150,f146])).

fof(f138,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f137,f122])).

fof(f137,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f45,f122])).

fof(f45,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.16/0.52  % (21190)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.16/0.52  % (21175)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.16/0.53  % (21174)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.53  % (21182)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.16/0.53  % (21176)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.54  % (21181)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.16/0.54  % (21178)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.54  % (21199)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.16/0.54  % (21196)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.16/0.54  % (21197)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.16/0.54  % (21189)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.54  % (21180)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.54  % (21172)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (21183)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.55  % (21188)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  % (21185)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.55  % (21186)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.55  % (21188)Refutation not found, incomplete strategy% (21188)------------------------------
% 1.30/0.55  % (21188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (21188)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (21188)Memory used [KB]: 10746
% 1.30/0.55  % (21188)Time elapsed: 0.122 s
% 1.30/0.55  % (21188)------------------------------
% 1.30/0.55  % (21188)------------------------------
% 1.30/0.55  % (21187)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (21198)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.56  % (21177)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.30/0.56  % (21200)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.56  % (21195)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.56  % (21184)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.56  % (21192)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.56  % (21193)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.56  % (21179)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.56  % (21194)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.57  % (21201)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.57  % (21197)Refutation found. Thanks to Tanya!
% 1.30/0.57  % SZS status Theorem for theBenchmark
% 1.30/0.57  % SZS output start Proof for theBenchmark
% 1.30/0.57  fof(f650,plain,(
% 1.30/0.57    $false),
% 1.30/0.57    inference(avatar_sat_refutation,[],[f153,f211,f242,f258,f649])).
% 1.30/0.57  fof(f649,plain,(
% 1.30/0.57    ~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_5),
% 1.30/0.57    inference(avatar_contradiction_clause,[],[f645])).
% 1.30/0.57  fof(f645,plain,(
% 1.30/0.57    $false | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f301,f561])).
% 1.30/0.57  fof(f561,plain,(
% 1.30/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl2_2 | ~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f553,f528])).
% 1.30/0.57  fof(f528,plain,(
% 1.30/0.57    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f369,f503])).
% 1.30/0.57  fof(f503,plain,(
% 1.30/0.57    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f324,f367,f79])).
% 1.30/0.57  fof(f79,plain,(
% 1.30/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.30/0.57    inference(cnf_transformation,[],[f42])).
% 1.30/0.57  fof(f42,plain,(
% 1.30/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.30/0.57    inference(flattening,[],[f41])).
% 1.30/0.57  fof(f41,plain,(
% 1.30/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.57    inference(ennf_transformation,[],[f3])).
% 1.30/0.57  fof(f3,axiom,(
% 1.30/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.30/0.57  fof(f367,plain,(
% 1.30/0.57    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f291,f232])).
% 1.30/0.57  fof(f232,plain,(
% 1.30/0.57    k1_xboole_0 = sK1 | ~spl2_3),
% 1.30/0.57    inference(avatar_component_clause,[],[f230])).
% 1.30/0.57  fof(f230,plain,(
% 1.30/0.57    spl2_3 <=> k1_xboole_0 = sK1),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.30/0.57  fof(f291,plain,(
% 1.30/0.57    k1_xboole_0 = k2_relat_1(k2_funct_1(sK1)) | ~spl2_5),
% 1.30/0.57    inference(backward_demodulation,[],[f207,f259])).
% 1.30/0.57  fof(f259,plain,(
% 1.30/0.57    k1_xboole_0 = sK0 | ~spl2_5),
% 1.30/0.57    inference(backward_demodulation,[],[f154,f240])).
% 1.30/0.57  fof(f240,plain,(
% 1.30/0.57    k1_xboole_0 = k2_relat_1(sK1) | ~spl2_5),
% 1.30/0.57    inference(avatar_component_clause,[],[f239])).
% 1.30/0.57  fof(f239,plain,(
% 1.30/0.57    spl2_5 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.30/0.57  fof(f154,plain,(
% 1.30/0.57    sK0 = k2_relat_1(sK1)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f118,f116,f120,f76])).
% 1.30/0.57  fof(f76,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f39])).
% 1.30/0.57  fof(f39,plain,(
% 1.30/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.57    inference(flattening,[],[f38])).
% 1.30/0.57  fof(f38,plain,(
% 1.30/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.30/0.57    inference(ennf_transformation,[],[f15])).
% 1.30/0.57  fof(f15,axiom,(
% 1.30/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.30/0.57  fof(f120,plain,(
% 1.30/0.57    v5_relat_1(sK1,sK0)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f49,f83])).
% 1.30/0.57  fof(f83,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f44])).
% 1.30/0.57  fof(f44,plain,(
% 1.30/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(ennf_transformation,[],[f9])).
% 1.30/0.57  fof(f9,axiom,(
% 1.30/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.30/0.57  fof(f49,plain,(
% 1.30/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.30/0.57    inference(cnf_transformation,[],[f23])).
% 1.30/0.57  fof(f23,plain,(
% 1.30/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.30/0.57    inference(flattening,[],[f22])).
% 1.30/0.57  fof(f22,plain,(
% 1.30/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.30/0.57    inference(ennf_transformation,[],[f21])).
% 1.30/0.57  fof(f21,negated_conjecture,(
% 1.30/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.30/0.57    inference(negated_conjecture,[],[f20])).
% 1.30/0.57  fof(f20,conjecture,(
% 1.30/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.30/0.57  fof(f116,plain,(
% 1.30/0.57    v2_funct_2(sK1,sK0)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f48,f49,f61])).
% 1.30/0.57  fof(f61,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f33])).
% 1.30/0.57  fof(f33,plain,(
% 1.30/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(flattening,[],[f32])).
% 1.30/0.57  fof(f32,plain,(
% 1.30/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(ennf_transformation,[],[f13])).
% 1.30/0.57  fof(f13,axiom,(
% 1.30/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.30/0.57  fof(f48,plain,(
% 1.30/0.57    v3_funct_2(sK1,sK0,sK0)),
% 1.30/0.57    inference(cnf_transformation,[],[f23])).
% 1.30/0.57  fof(f46,plain,(
% 1.30/0.57    v1_funct_1(sK1)),
% 1.30/0.57    inference(cnf_transformation,[],[f23])).
% 1.30/0.57  fof(f118,plain,(
% 1.30/0.57    v1_relat_1(sK1)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f49,f81])).
% 1.30/0.57  fof(f81,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f43])).
% 1.30/0.57  fof(f43,plain,(
% 1.30/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(ennf_transformation,[],[f8])).
% 1.30/0.57  fof(f8,axiom,(
% 1.30/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.30/0.57  fof(f207,plain,(
% 1.30/0.57    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f179,f177,f181,f76])).
% 1.30/0.57  fof(f181,plain,(
% 1.30/0.57    v5_relat_1(k2_funct_1(sK1),sK0)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f136,f83])).
% 1.30/0.57  fof(f136,plain,(
% 1.30/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.30/0.57    inference(backward_demodulation,[],[f126,f122])).
% 1.30/0.57  fof(f122,plain,(
% 1.30/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f58])).
% 1.30/0.57  fof(f58,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f31])).
% 1.30/0.57  fof(f31,plain,(
% 1.30/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.30/0.57    inference(flattening,[],[f30])).
% 1.30/0.57  fof(f30,plain,(
% 1.30/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.30/0.57    inference(ennf_transformation,[],[f18])).
% 1.30/0.57  fof(f18,axiom,(
% 1.30/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.30/0.57  fof(f47,plain,(
% 1.30/0.57    v1_funct_2(sK1,sK0,sK0)),
% 1.30/0.57    inference(cnf_transformation,[],[f23])).
% 1.30/0.57  fof(f126,plain,(
% 1.30/0.57    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f57])).
% 1.30/0.57  fof(f57,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f29])).
% 1.30/0.57  fof(f29,plain,(
% 1.30/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.30/0.57    inference(flattening,[],[f28])).
% 1.30/0.57  fof(f28,plain,(
% 1.30/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.30/0.57    inference(ennf_transformation,[],[f16])).
% 1.30/0.57  fof(f16,axiom,(
% 1.30/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.30/0.57  fof(f177,plain,(
% 1.30/0.57    v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f133,f135,f136,f61])).
% 1.30/0.57  fof(f135,plain,(
% 1.30/0.57    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.30/0.57    inference(backward_demodulation,[],[f125,f122])).
% 1.30/0.57  fof(f125,plain,(
% 1.30/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f56])).
% 1.30/0.57  fof(f56,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f29])).
% 1.30/0.57  fof(f133,plain,(
% 1.30/0.57    v1_funct_1(k2_funct_1(sK1))),
% 1.30/0.57    inference(backward_demodulation,[],[f123,f122])).
% 1.30/0.57  fof(f123,plain,(
% 1.30/0.57    v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f48,f47,f49,f54])).
% 1.30/0.57  fof(f54,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f29])).
% 1.30/0.57  fof(f179,plain,(
% 1.30/0.57    v1_relat_1(k2_funct_1(sK1))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f136,f81])).
% 1.30/0.57  fof(f324,plain,(
% 1.30/0.57    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl2_3),
% 1.30/0.57    inference(backward_demodulation,[],[f179,f232])).
% 1.30/0.57  fof(f369,plain,(
% 1.30/0.57    k1_xboole_0 = k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f296,f232])).
% 1.30/0.57  fof(f296,plain,(
% 1.30/0.57    k1_xboole_0 = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl2_5),
% 1.30/0.57    inference(forward_demodulation,[],[f276,f91])).
% 1.30/0.57  fof(f91,plain,(
% 1.30/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.30/0.57    inference(definition_unfolding,[],[f72,f52])).
% 1.30/0.57  fof(f52,plain,(
% 1.30/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f19])).
% 1.30/0.57  fof(f19,axiom,(
% 1.30/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.30/0.57  fof(f72,plain,(
% 1.30/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.30/0.57    inference(cnf_transformation,[],[f5])).
% 1.30/0.57  fof(f5,axiom,(
% 1.30/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.30/0.57  fof(f276,plain,(
% 1.30/0.57    k6_partfun1(k1_xboole_0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl2_5),
% 1.30/0.57    inference(backward_demodulation,[],[f155,f259])).
% 1.30/0.57  fof(f155,plain,(
% 1.30/0.57    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.30/0.57    inference(backward_demodulation,[],[f141,f154])).
% 1.30/0.57  fof(f141,plain,(
% 1.30/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f115,f118,f92])).
% 1.30/0.57  fof(f92,plain,(
% 1.30/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))) )),
% 1.30/0.57    inference(definition_unfolding,[],[f74,f52])).
% 1.30/0.57  fof(f74,plain,(
% 1.30/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f37])).
% 1.30/0.57  fof(f37,plain,(
% 1.30/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.57    inference(flattening,[],[f36])).
% 1.30/0.57  fof(f36,plain,(
% 1.30/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.57    inference(ennf_transformation,[],[f7])).
% 1.30/0.57  fof(f7,axiom,(
% 1.30/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.30/0.57  fof(f115,plain,(
% 1.30/0.57    v2_funct_1(sK1)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f48,f49,f60])).
% 1.30/0.57  fof(f60,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f33])).
% 1.30/0.57  fof(f553,plain,(
% 1.30/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (spl2_2 | ~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f373,f506])).
% 1.30/0.57  fof(f506,plain,(
% 1.30/0.57    k6_partfun1(k1_relat_1(k1_xboole_0)) = k5_relat_1(k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f314,f503])).
% 1.30/0.57  fof(f314,plain,(
% 1.30/0.57    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0)) | ~spl2_3),
% 1.30/0.57    inference(backward_demodulation,[],[f140,f232])).
% 1.30/0.57  fof(f140,plain,(
% 1.30/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f115,f118,f93])).
% 1.30/0.57  fof(f93,plain,(
% 1.30/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))) )),
% 1.30/0.57    inference(definition_unfolding,[],[f73,f52])).
% 1.30/0.57  fof(f73,plain,(
% 1.30/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f37])).
% 1.30/0.57  fof(f373,plain,(
% 1.30/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) | (spl2_2 | ~spl2_3 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f300,f232])).
% 1.30/0.57  fof(f300,plain,(
% 1.30/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) | (spl2_2 | ~spl2_5)),
% 1.30/0.57    inference(forward_demodulation,[],[f293,f91])).
% 1.30/0.57  fof(f293,plain,(
% 1.30/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) | (spl2_2 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f212,f259])).
% 1.30/0.57  fof(f212,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | spl2_2),
% 1.30/0.57    inference(forward_demodulation,[],[f152,f199])).
% 1.30/0.57  fof(f199,plain,(
% 1.30/0.57    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 1.30/0.57    inference(forward_demodulation,[],[f174,f140])).
% 1.30/0.57  fof(f174,plain,(
% 1.30/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f49,f133,f136,f53])).
% 1.30/0.57  fof(f53,plain,(
% 1.30/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f27])).
% 1.30/0.57  fof(f27,plain,(
% 1.30/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.30/0.57    inference(flattening,[],[f26])).
% 1.30/0.57  fof(f26,plain,(
% 1.30/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.30/0.57    inference(ennf_transformation,[],[f17])).
% 1.30/0.57  fof(f17,axiom,(
% 1.30/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.30/0.57  fof(f152,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl2_2),
% 1.30/0.57    inference(avatar_component_clause,[],[f150])).
% 1.30/0.57  fof(f150,plain,(
% 1.30/0.57    spl2_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.30/0.57  fof(f301,plain,(
% 1.30/0.57    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl2_1 | ~spl2_5)),
% 1.30/0.57    inference(forward_demodulation,[],[f294,f91])).
% 1.30/0.57  fof(f294,plain,(
% 1.30/0.57    r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) | (~spl2_1 | ~spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f213,f259])).
% 1.30/0.57  fof(f213,plain,(
% 1.30/0.57    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl2_1),
% 1.30/0.57    inference(forward_demodulation,[],[f147,f200])).
% 1.30/0.57  fof(f200,plain,(
% 1.30/0.57    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.30/0.57    inference(forward_demodulation,[],[f172,f155])).
% 1.30/0.57  fof(f172,plain,(
% 1.30/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f46,f133,f49,f136,f53])).
% 1.30/0.57  fof(f147,plain,(
% 1.30/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~spl2_1),
% 1.30/0.57    inference(avatar_component_clause,[],[f146])).
% 1.30/0.57  fof(f146,plain,(
% 1.30/0.57    spl2_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.30/0.57  fof(f258,plain,(
% 1.30/0.57    spl2_2 | spl2_5),
% 1.30/0.57    inference(avatar_contradiction_clause,[],[f254])).
% 1.30/0.57  fof(f254,plain,(
% 1.30/0.57    $false | (spl2_2 | spl2_5)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f86,f249,f101])).
% 1.30/0.57  fof(f101,plain,(
% 1.30/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.30/0.57    inference(duplicate_literal_removal,[],[f94])).
% 1.30/0.57  fof(f94,plain,(
% 1.30/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.30/0.57    inference(equality_resolution,[],[f50])).
% 1.30/0.57  fof(f50,plain,(
% 1.30/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f25])).
% 1.30/0.57  fof(f25,plain,(
% 1.30/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(flattening,[],[f24])).
% 1.30/0.57  fof(f24,plain,(
% 1.30/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.30/0.57    inference(ennf_transformation,[],[f11])).
% 1.30/0.57  fof(f11,axiom,(
% 1.30/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.30/0.57  fof(f249,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl2_2 | spl2_5)),
% 1.30/0.57    inference(backward_demodulation,[],[f212,f248])).
% 1.30/0.57  fof(f248,plain,(
% 1.30/0.57    sK0 = k1_relat_1(sK1) | spl2_5),
% 1.30/0.57    inference(backward_demodulation,[],[f117,f244])).
% 1.30/0.57  fof(f244,plain,(
% 1.30/0.57    sK0 = k1_relset_1(sK0,sK0,sK1) | spl2_5),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f47,f49,f243,f67])).
% 1.30/0.57  fof(f67,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f35])).
% 1.30/0.57  fof(f35,plain,(
% 1.30/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(flattening,[],[f34])).
% 1.30/0.57  fof(f34,plain,(
% 1.30/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(ennf_transformation,[],[f14])).
% 1.30/0.57  fof(f14,axiom,(
% 1.30/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.30/0.57  fof(f243,plain,(
% 1.30/0.57    k1_xboole_0 != sK0 | spl2_5),
% 1.30/0.57    inference(superposition,[],[f241,f154])).
% 1.30/0.57  fof(f241,plain,(
% 1.30/0.57    k1_xboole_0 != k2_relat_1(sK1) | spl2_5),
% 1.30/0.57    inference(avatar_component_clause,[],[f239])).
% 1.30/0.57  fof(f117,plain,(
% 1.30/0.57    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f49,f77])).
% 1.30/0.57  fof(f77,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f40])).
% 1.30/0.57  fof(f40,plain,(
% 1.30/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.57    inference(ennf_transformation,[],[f10])).
% 1.30/0.57  fof(f10,axiom,(
% 1.30/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.30/0.57  fof(f86,plain,(
% 1.30/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.30/0.57    inference(definition_unfolding,[],[f59,f52])).
% 1.30/0.57  fof(f59,plain,(
% 1.30/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f12])).
% 1.30/0.57  fof(f12,axiom,(
% 1.30/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.30/0.57  fof(f242,plain,(
% 1.30/0.57    spl2_3 | ~spl2_5),
% 1.30/0.57    inference(avatar_split_clause,[],[f143,f239,f230])).
% 1.30/0.57  fof(f143,plain,(
% 1.30/0.57    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = sK1),
% 1.30/0.57    inference(resolution,[],[f118,f79])).
% 1.30/0.57  fof(f211,plain,(
% 1.30/0.57    spl2_1),
% 1.30/0.57    inference(avatar_contradiction_clause,[],[f210])).
% 1.30/0.57  fof(f210,plain,(
% 1.30/0.57    $false | spl2_1),
% 1.30/0.57    inference(unit_resulting_resolution,[],[f86,f201,f101])).
% 1.30/0.57  fof(f201,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl2_1),
% 1.30/0.57    inference(backward_demodulation,[],[f148,f200])).
% 1.30/0.57  fof(f148,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl2_1),
% 1.30/0.57    inference(avatar_component_clause,[],[f146])).
% 1.30/0.57  fof(f153,plain,(
% 1.30/0.57    ~spl2_1 | ~spl2_2),
% 1.30/0.57    inference(avatar_split_clause,[],[f138,f150,f146])).
% 1.30/0.57  fof(f138,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.30/0.57    inference(forward_demodulation,[],[f137,f122])).
% 1.30/0.57  fof(f137,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.30/0.57    inference(backward_demodulation,[],[f45,f122])).
% 1.30/0.57  fof(f45,plain,(
% 1.30/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 1.30/0.57    inference(cnf_transformation,[],[f23])).
% 1.30/0.57  % SZS output end Proof for theBenchmark
% 1.30/0.57  % (21197)------------------------------
% 1.30/0.57  % (21197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (21197)Termination reason: Refutation
% 1.30/0.57  
% 1.30/0.57  % (21197)Memory used [KB]: 6524
% 1.30/0.57  % (21197)Time elapsed: 0.146 s
% 1.30/0.57  % (21197)------------------------------
% 1.30/0.57  % (21197)------------------------------
% 1.30/0.57  % (21171)Success in time 0.197 s
%------------------------------------------------------------------------------
