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
% DateTime   : Thu Dec  3 13:03:18 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 447 expanded)
%              Number of leaves         :   18 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  320 (2053 expanded)
%              Number of equality atoms :   74 ( 494 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f144,f247,f372,f531,f632,f834])).

fof(f834,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f831])).

fof(f831,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f733,f803])).

fof(f803,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f729,f780])).

fof(f780,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f646,f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f646,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f111,f305])).

fof(f305,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f266,f47])).

fof(f266,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f253,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f253,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f101,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f111,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f100,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f100,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f37,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f729,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f695,f290])).

fof(f290,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f48,f279,f47])).

fof(f279,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f38,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f38,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f695,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,k1_xboole_0)
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f652,f83])).

fof(f652,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1)
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f143,f305])).

fof(f143,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_5
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f733,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f688,f80])).

fof(f688,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f635,f83])).

fof(f635,plain,
    ( v1_funct_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f36,f305])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f632,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f110,f139])).

fof(f139,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_4
  <=> v1_funct_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f110,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(forward_demodulation,[],[f93,f95])).

fof(f95,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f35,f37,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f37,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f531,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f84,f143,f134,f516,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f516,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f445,f507])).

fof(f507,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f38,f408])).

fof(f408,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK3,X1)) = X1 )
    | spl4_2 ),
    inference(backward_demodulation,[],[f116,f405])).

fof(f405,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_2 ),
    inference(backward_demodulation,[],[f97,f398])).

fof(f398,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f84,f36,f37,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f37,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f116,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK3))
      | k1_relat_1(k7_relat_1(sK3,X1)) = X1 ) ),
    inference(resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f445,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f134,f59])).

fof(f134,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_3
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f84,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f372,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f48,f300])).

fof(f300,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | spl4_3 ),
    inference(forward_demodulation,[],[f292,f114])).

fof(f114,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f100,f57])).

fof(f292,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ spl4_1
    | spl4_3 ),
    inference(backward_demodulation,[],[f206,f290])).

fof(f206,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f135,f109,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f94,f95])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f35,f37,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f135,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f247,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f65,f240])).

fof(f240,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f206,f231])).

fof(f231,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f38,f119])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK3,X1)) = X1 )
    | spl4_2 ),
    inference(forward_demodulation,[],[f116,f104])).

fof(f104,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_2 ),
    inference(backward_demodulation,[],[f97,f96])).

fof(f96,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f84,f36,f37,f56])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f144,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f108,f141,f137,f133])).

fof(f108,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f107,f95])).

fof(f107,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    inference(forward_demodulation,[],[f106,f95])).

fof(f106,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    inference(backward_demodulation,[],[f33,f95])).

fof(f33,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f82,f78])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (22291)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (22298)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (22316)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.54  % (22300)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (22293)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (22290)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (22297)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.55  % (22314)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.55  % (22296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.55  % (22301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (22306)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (22292)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  % (22295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.56  % (22304)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (22309)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (22312)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (22288)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.56  % (22289)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.45/0.57  % (22317)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.57  % (22303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.57  % (22310)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.57  % (22313)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.57  % (22302)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.58  % (22299)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.58  % (22294)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.59  % (22307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.59  % (22292)Refutation found. Thanks to Tanya!
% 1.45/0.59  % SZS status Theorem for theBenchmark
% 1.45/0.59  % SZS output start Proof for theBenchmark
% 1.45/0.59  fof(f835,plain,(
% 1.45/0.59    $false),
% 1.45/0.59    inference(avatar_sat_refutation,[],[f85,f144,f247,f372,f531,f632,f834])).
% 1.45/0.59  fof(f834,plain,(
% 1.45/0.59    ~spl4_1 | ~spl4_2 | spl4_5),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f831])).
% 1.45/0.59  fof(f831,plain,(
% 1.45/0.59    $false | (~spl4_1 | ~spl4_2 | spl4_5)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f733,f803])).
% 1.45/0.59  fof(f803,plain,(
% 1.45/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_5)),
% 1.45/0.59    inference(backward_demodulation,[],[f729,f780])).
% 1.45/0.59  fof(f780,plain,(
% 1.45/0.59    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f48,f646,f47])).
% 1.45/0.59  fof(f47,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.45/0.59    inference(cnf_transformation,[],[f3])).
% 1.45/0.59  fof(f3,axiom,(
% 1.45/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.59  fof(f646,plain,(
% 1.45/0.59    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f111,f305])).
% 1.45/0.59  fof(f305,plain,(
% 1.45/0.59    k1_xboole_0 = sK3 | ~spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f48,f266,f47])).
% 1.45/0.59  fof(f266,plain,(
% 1.45/0.59    r1_tarski(sK3,k1_xboole_0) | ~spl4_2),
% 1.45/0.59    inference(forward_demodulation,[],[f253,f62])).
% 1.45/0.59  fof(f62,plain,(
% 1.45/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.45/0.59    inference(equality_resolution,[],[f44])).
% 1.45/0.59  fof(f44,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f5])).
% 1.45/0.59  fof(f5,axiom,(
% 1.45/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.45/0.59  fof(f253,plain,(
% 1.45/0.59    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f101,f83])).
% 1.45/0.59  fof(f83,plain,(
% 1.45/0.59    k1_xboole_0 = sK1 | ~spl4_2),
% 1.45/0.59    inference(avatar_component_clause,[],[f82])).
% 1.45/0.59  fof(f82,plain,(
% 1.45/0.59    spl4_2 <=> k1_xboole_0 = sK1),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.45/0.59  fof(f101,plain,(
% 1.45/0.59    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f37,f50])).
% 1.45/0.59  fof(f50,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f6])).
% 1.45/0.59  fof(f6,axiom,(
% 1.45/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.45/0.59  fof(f37,plain,(
% 1.45/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f19,plain,(
% 1.45/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.45/0.59    inference(flattening,[],[f18])).
% 1.45/0.59  fof(f18,plain,(
% 1.45/0.59    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.45/0.59    inference(ennf_transformation,[],[f17])).
% 1.45/0.59  fof(f17,negated_conjecture,(
% 1.45/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.45/0.59    inference(negated_conjecture,[],[f16])).
% 1.45/0.59  fof(f16,conjecture,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.45/0.59  fof(f111,plain,(
% 1.45/0.59    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f100,f58])).
% 1.45/0.59  fof(f58,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f28])).
% 1.45/0.59  fof(f28,plain,(
% 1.45/0.59    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f8])).
% 1.45/0.59  fof(f8,axiom,(
% 1.45/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.45/0.59  fof(f100,plain,(
% 1.45/0.59    v1_relat_1(sK3)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f37,f61])).
% 1.45/0.59  fof(f61,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f32])).
% 1.45/0.59  fof(f32,plain,(
% 1.45/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.59    inference(ennf_transformation,[],[f10])).
% 1.45/0.59  fof(f10,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.45/0.59  fof(f48,plain,(
% 1.45/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f4])).
% 1.45/0.59  fof(f4,axiom,(
% 1.45/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.45/0.59  fof(f729,plain,(
% 1.45/0.59    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_5)),
% 1.45/0.59    inference(backward_demodulation,[],[f695,f290])).
% 1.45/0.59  fof(f290,plain,(
% 1.45/0.59    k1_xboole_0 = sK2 | ~spl4_1),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f48,f279,f47])).
% 1.45/0.59  fof(f279,plain,(
% 1.45/0.59    r1_tarski(sK2,k1_xboole_0) | ~spl4_1),
% 1.45/0.59    inference(backward_demodulation,[],[f38,f80])).
% 1.45/0.59  fof(f80,plain,(
% 1.45/0.59    k1_xboole_0 = sK0 | ~spl4_1),
% 1.45/0.59    inference(avatar_component_clause,[],[f78])).
% 1.45/0.59  fof(f78,plain,(
% 1.45/0.59    spl4_1 <=> k1_xboole_0 = sK0),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.45/0.59  fof(f38,plain,(
% 1.45/0.59    r1_tarski(sK2,sK0)),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f695,plain,(
% 1.45/0.59    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,k1_xboole_0) | (~spl4_2 | spl4_5)),
% 1.45/0.59    inference(backward_demodulation,[],[f652,f83])).
% 1.45/0.59  fof(f652,plain,(
% 1.45/0.59    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1) | (~spl4_2 | spl4_5)),
% 1.45/0.59    inference(backward_demodulation,[],[f143,f305])).
% 1.45/0.59  fof(f143,plain,(
% 1.45/0.59    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_5),
% 1.45/0.59    inference(avatar_component_clause,[],[f141])).
% 1.45/0.59  fof(f141,plain,(
% 1.45/0.59    spl4_5 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.45/0.59  fof(f733,plain,(
% 1.45/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 1.45/0.59    inference(backward_demodulation,[],[f688,f80])).
% 1.45/0.59  fof(f688,plain,(
% 1.45/0.59    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f635,f83])).
% 1.45/0.59  fof(f635,plain,(
% 1.45/0.59    v1_funct_2(k1_xboole_0,sK0,sK1) | ~spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f36,f305])).
% 1.45/0.59  fof(f36,plain,(
% 1.45/0.59    v1_funct_2(sK3,sK0,sK1)),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f632,plain,(
% 1.45/0.59    spl4_4),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f629])).
% 1.45/0.59  fof(f629,plain,(
% 1.45/0.59    $false | spl4_4),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f110,f139])).
% 1.45/0.59  fof(f139,plain,(
% 1.45/0.59    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_4),
% 1.45/0.59    inference(avatar_component_clause,[],[f137])).
% 1.45/0.59  fof(f137,plain,(
% 1.45/0.59    spl4_4 <=> v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.45/0.59  fof(f110,plain,(
% 1.45/0.59    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.45/0.59    inference(forward_demodulation,[],[f93,f95])).
% 1.45/0.59  fof(f95,plain,(
% 1.45/0.59    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) )),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f35,f37,f41])).
% 1.45/0.59  fof(f41,plain,(
% 1.45/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f23])).
% 1.45/0.59  fof(f23,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.45/0.59    inference(flattening,[],[f22])).
% 1.45/0.59  fof(f22,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.45/0.59    inference(ennf_transformation,[],[f15])).
% 1.45/0.59  fof(f15,axiom,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.45/0.59  fof(f35,plain,(
% 1.45/0.59    v1_funct_1(sK3)),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f93,plain,(
% 1.45/0.59    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f35,f37,f39])).
% 1.45/0.59  fof(f39,plain,(
% 1.45/0.59    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f21])).
% 1.45/0.59  fof(f21,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.45/0.59    inference(flattening,[],[f20])).
% 1.45/0.59  fof(f20,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.45/0.59    inference(ennf_transformation,[],[f14])).
% 1.45/0.59  fof(f14,axiom,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.45/0.59  fof(f531,plain,(
% 1.45/0.59    spl4_2 | ~spl4_3 | spl4_5),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f522])).
% 1.45/0.59  fof(f522,plain,(
% 1.45/0.59    $false | (spl4_2 | ~spl4_3 | spl4_5)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f84,f143,f134,f516,f55])).
% 1.45/0.59  fof(f55,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f25])).
% 1.45/0.59  fof(f25,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.59    inference(flattening,[],[f24])).
% 1.45/0.59  fof(f24,plain,(
% 1.45/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.59    inference(ennf_transformation,[],[f13])).
% 1.45/0.59  fof(f13,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.45/0.59  fof(f516,plain,(
% 1.45/0.59    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3)),
% 1.45/0.59    inference(backward_demodulation,[],[f445,f507])).
% 1.45/0.59  fof(f507,plain,(
% 1.45/0.59    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f38,f408])).
% 1.45/0.59  fof(f408,plain,(
% 1.45/0.59    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK3,X1)) = X1) ) | spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f116,f405])).
% 1.45/0.59  fof(f405,plain,(
% 1.45/0.59    sK0 = k1_relat_1(sK3) | spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f97,f398])).
% 1.45/0.59  fof(f398,plain,(
% 1.45/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f84,f36,f37,f56])).
% 1.45/0.59  fof(f56,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f25])).
% 1.45/0.59  fof(f97,plain,(
% 1.45/0.59    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f37,f59])).
% 1.45/0.59  fof(f59,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f29])).
% 1.45/0.59  fof(f29,plain,(
% 1.45/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.59    inference(ennf_transformation,[],[f11])).
% 1.45/0.59  fof(f11,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.45/0.59  fof(f116,plain,(
% 1.45/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X1)) = X1) )),
% 1.45/0.59    inference(resolution,[],[f100,f57])).
% 1.45/0.59  fof(f57,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.45/0.59    inference(cnf_transformation,[],[f27])).
% 1.45/0.59  fof(f27,plain,(
% 1.45/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.45/0.59    inference(flattening,[],[f26])).
% 1.45/0.59  fof(f26,plain,(
% 1.45/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f9])).
% 1.45/0.59  fof(f9,axiom,(
% 1.45/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.45/0.59  fof(f445,plain,(
% 1.45/0.59    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_3),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f134,f59])).
% 1.45/0.59  fof(f134,plain,(
% 1.45/0.59    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.45/0.59    inference(avatar_component_clause,[],[f133])).
% 1.45/0.59  fof(f133,plain,(
% 1.45/0.59    spl4_3 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.45/0.59  fof(f84,plain,(
% 1.45/0.59    k1_xboole_0 != sK1 | spl4_2),
% 1.45/0.59    inference(avatar_component_clause,[],[f82])).
% 1.45/0.59  fof(f372,plain,(
% 1.45/0.59    ~spl4_1 | spl4_3),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f364])).
% 1.45/0.59  fof(f364,plain,(
% 1.45/0.59    $false | (~spl4_1 | spl4_3)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f48,f300])).
% 1.45/0.59  fof(f300,plain,(
% 1.45/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_1 | spl4_3)),
% 1.45/0.59    inference(forward_demodulation,[],[f292,f114])).
% 1.45/0.59  fof(f114,plain,(
% 1.45/0.59    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f48,f100,f57])).
% 1.45/0.59  fof(f292,plain,(
% 1.45/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) | (~spl4_1 | spl4_3)),
% 1.45/0.59    inference(backward_demodulation,[],[f206,f290])).
% 1.45/0.59  fof(f206,plain,(
% 1.45/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_3),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f135,f109,f60])).
% 1.45/0.59  fof(f60,plain,(
% 1.45/0.59    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f31])).
% 1.45/0.59  fof(f31,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.45/0.59    inference(flattening,[],[f30])).
% 1.45/0.59  fof(f30,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.45/0.59    inference(ennf_transformation,[],[f12])).
% 1.45/0.59  fof(f12,axiom,(
% 1.45/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 1.45/0.59  fof(f109,plain,(
% 1.45/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.45/0.59    inference(forward_demodulation,[],[f94,f95])).
% 1.45/0.59  fof(f94,plain,(
% 1.45/0.59    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f35,f37,f40])).
% 1.45/0.59  fof(f40,plain,(
% 1.45/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f21])).
% 1.45/0.59  fof(f135,plain,(
% 1.45/0.59    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.45/0.59    inference(avatar_component_clause,[],[f133])).
% 1.45/0.59  fof(f247,plain,(
% 1.45/0.59    spl4_2 | spl4_3),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f241])).
% 1.45/0.59  fof(f241,plain,(
% 1.45/0.59    $false | (spl4_2 | spl4_3)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f65,f240])).
% 1.45/0.59  fof(f240,plain,(
% 1.45/0.59    ~r1_tarski(sK2,sK2) | (spl4_2 | spl4_3)),
% 1.45/0.59    inference(backward_demodulation,[],[f206,f231])).
% 1.45/0.59  fof(f231,plain,(
% 1.45/0.59    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f38,f119])).
% 1.45/0.59  fof(f119,plain,(
% 1.45/0.59    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK3,X1)) = X1) ) | spl4_2),
% 1.45/0.59    inference(forward_demodulation,[],[f116,f104])).
% 1.45/0.59  fof(f104,plain,(
% 1.45/0.59    sK0 = k1_relat_1(sK3) | spl4_2),
% 1.45/0.59    inference(backward_demodulation,[],[f97,f96])).
% 1.45/0.59  fof(f96,plain,(
% 1.45/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f84,f36,f37,f56])).
% 1.45/0.59  fof(f65,plain,(
% 1.45/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.59    inference(equality_resolution,[],[f45])).
% 1.45/0.59  fof(f45,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.45/0.59    inference(cnf_transformation,[],[f3])).
% 1.45/0.59  fof(f144,plain,(
% 1.45/0.59    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 1.45/0.59    inference(avatar_split_clause,[],[f108,f141,f137,f133])).
% 1.45/0.59  fof(f108,plain,(
% 1.45/0.59    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.45/0.59    inference(forward_demodulation,[],[f107,f95])).
% 1.45/0.59  fof(f107,plain,(
% 1.45/0.59    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.45/0.59    inference(forward_demodulation,[],[f106,f95])).
% 1.45/0.59  fof(f106,plain,(
% 1.45/0.59    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.45/0.59    inference(backward_demodulation,[],[f33,f95])).
% 1.45/0.59  fof(f33,plain,(
% 1.45/0.59    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f85,plain,(
% 1.45/0.59    spl4_1 | ~spl4_2),
% 1.45/0.59    inference(avatar_split_clause,[],[f34,f82,f78])).
% 1.45/0.59  fof(f34,plain,(
% 1.45/0.59    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  % SZS output end Proof for theBenchmark
% 1.45/0.59  % (22292)------------------------------
% 1.45/0.59  % (22292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (22292)Termination reason: Refutation
% 1.45/0.59  
% 1.45/0.59  % (22292)Memory used [KB]: 6524
% 1.45/0.59  % (22292)Time elapsed: 0.157 s
% 1.45/0.59  % (22292)------------------------------
% 1.45/0.59  % (22292)------------------------------
% 1.45/0.59  % (22287)Success in time 0.234 s
%------------------------------------------------------------------------------
