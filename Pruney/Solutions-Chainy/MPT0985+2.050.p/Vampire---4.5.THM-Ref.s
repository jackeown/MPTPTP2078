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
% DateTime   : Thu Dec  3 13:02:07 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  190 (1261 expanded)
%              Number of leaves         :   29 ( 338 expanded)
%              Depth                    :   18
%              Number of atoms          :  615 (7027 expanded)
%              Number of equality atoms :  165 (1132 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f191,f256,f258,f426,f614,f628,f721,f730,f861,f900,f1306])).

fof(f1306,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f1305])).

fof(f1305,plain,
    ( $false
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f1304,f854])).

fof(f854,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f817,f155])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
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

fof(f817,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f738,f249])).

fof(f249,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f738,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f84,f255])).

fof(f255,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f69])).

fof(f69,plain,
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
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
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

fof(f1304,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f1297,f155])).

fof(f1297,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f736,f729,f1003,f891,f158])).

fof(f158,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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

fof(f891,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f826,f880])).

fof(f880,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f750,f879])).

fof(f879,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl8_6
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f717,f255])).

fof(f717,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl8_24
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f750,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f207,f255])).

fof(f207,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f85,f82,f184,f112])).

fof(f112,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f184,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f84,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f826,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f755,f249])).

fof(f755,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f220,f255])).

fof(f220,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f202,f189])).

fof(f189,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f185,f86])).

fof(f86,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f185,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f84,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f202,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f82,f184,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1003,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f918,f940])).

fof(f940,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f939,f255])).

fof(f939,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f938,f143])).

fof(f143,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f89,f90])).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f89,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f938,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f421,f249])).

fof(f421,plain,
    ( k2_funct_1(sK2) = k6_partfun1(sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl8_11
  <=> k2_funct_1(sK2) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f918,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f917,f255])).

fof(f917,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f175,f249])).

fof(f175,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl8_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f729,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl8_25
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f736,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f82,f255])).

fof(f900,plain,
    ( ~ spl8_6
    | spl8_12
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f899])).

fof(f899,plain,
    ( $false
    | ~ spl8_6
    | spl8_12
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f887,f143])).

fof(f887,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | ~ spl8_6
    | spl8_12
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f783,f880])).

fof(f783,plain,
    ( k1_xboole_0 != k6_partfun1(k1_relat_1(k1_xboole_0))
    | ~ spl8_6
    | spl8_12 ),
    inference(backward_demodulation,[],[f425,f255])).

fof(f425,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl8_12
  <=> sK2 = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f861,plain,
    ( ~ spl8_1
    | spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | ~ spl8_1
    | spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f859,f855])).

fof(f855,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f820,f156])).

fof(f156,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f820,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f743,f249])).

fof(f743,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl8_3
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f179,f255])).

fof(f179,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl8_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f859,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f832,f156])).

fof(f832,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f769,f249])).

fof(f769,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))))
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f287,f255])).

fof(f287,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f286,f218])).

fof(f218,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f206,f189])).

fof(f206,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f85,f82,f184,f111])).

fof(f111,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f286,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f272,f207])).

fof(f272,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f170,f204,f108])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f204,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f82,f184,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f170,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f730,plain,
    ( spl8_25
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f313,f247,f727])).

fof(f313,plain,
    ( k1_xboole_0 != sK1
    | r1_tarski(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f312,f189])).

fof(f312,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f311,f184])).

fof(f311,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f225,f105])).

fof(f105,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f225,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f184,f186,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f186,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f84,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f721,plain,
    ( spl8_24
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f720,f247,f716])).

fof(f720,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f329,f204])).

fof(f329,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f104,f218])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f628,plain,
    ( ~ spl8_1
    | spl8_3
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl8_1
    | spl8_3
    | spl8_4 ),
    inference(subsumption_resolution,[],[f624,f287])).

fof(f624,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl8_1
    | spl8_3
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f170,f225,f245,f289,f179,f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f289,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f288,f218])).

fof(f288,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f271,f207])).

fof(f271,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f170,f204,f107])).

fof(f245,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_4
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f614,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f610,f287])).

fof(f610,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl8_1
    | spl8_2
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f170,f225,f175,f245,f289,f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f426,plain,
    ( spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f417,f423,f419])).

fof(f417,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f416,f189])).

fof(f416,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1) ),
    inference(forward_demodulation,[],[f415,f149])).

fof(f149,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f97,f90])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f415,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) ),
    inference(subsumption_resolution,[],[f414,f184])).

fof(f414,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f413,f82])).

fof(f413,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f412,f147])).

fof(f147,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f93,f90])).

fof(f93,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f412,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f411,f146])).

fof(f146,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f94,f90])).

fof(f94,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f411,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f409,f85])).

fof(f409,plain,
    ( sK2 != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = k6_partfun1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f152,f215])).

fof(f215,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f214,f189])).

fof(f214,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f184,f150])).

fof(f150,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f101,f90])).

fof(f101,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f152,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f115,f90])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f258,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f257,f247,f243])).

fof(f257,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f233,f184])).

fof(f233,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f104,f189])).

fof(f256,plain,
    ( spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f251,f247,f253])).

fof(f251,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f232,f184])).

fof(f232,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f103,f189])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f191,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f184,f181])).

fof(f181,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f82,f171,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f171,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f169])).

fof(f180,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f87,f177,f173,f169])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f70])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5018)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5035)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (5027)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (5024)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (5023)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (5016)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5015)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (5014)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (5043)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (5032)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (5019)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (5038)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (5042)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (5033)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (5017)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (5036)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (5030)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (5020)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (5037)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (5025)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (5029)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (5022)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (5039)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (5040)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (5041)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (5034)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (5021)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (5026)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (5031)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (5031)Refutation not found, incomplete strategy% (5031)------------------------------
% 0.22/0.57  % (5031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (5031)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (5031)Memory used [KB]: 10746
% 0.22/0.57  % (5031)Time elapsed: 0.163 s
% 0.22/0.57  % (5031)------------------------------
% 0.22/0.57  % (5031)------------------------------
% 0.22/0.59  % (5028)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.71/0.61  % (5040)Refutation found. Thanks to Tanya!
% 1.71/0.61  % SZS status Theorem for theBenchmark
% 1.71/0.61  % SZS output start Proof for theBenchmark
% 1.71/0.61  fof(f1307,plain,(
% 1.71/0.61    $false),
% 1.71/0.61    inference(avatar_sat_refutation,[],[f180,f191,f256,f258,f426,f614,f628,f721,f730,f861,f900,f1306])).
% 1.71/0.61  fof(f1306,plain,(
% 1.71/0.61    spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_11 | ~spl8_24 | ~spl8_25),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f1305])).
% 1.71/0.61  fof(f1305,plain,(
% 1.71/0.61    $false | (spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_11 | ~spl8_24 | ~spl8_25)),
% 1.71/0.61    inference(subsumption_resolution,[],[f1304,f854])).
% 1.71/0.61  fof(f854,plain,(
% 1.71/0.61    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(forward_demodulation,[],[f817,f155])).
% 1.71/0.61  fof(f155,plain,(
% 1.71/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.71/0.61    inference(equality_resolution,[],[f129])).
% 1.71/0.61  fof(f129,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.71/0.61    inference(cnf_transformation,[],[f81])).
% 1.71/0.61  fof(f81,plain,(
% 1.71/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.61    inference(flattening,[],[f80])).
% 1.71/0.61  fof(f80,plain,(
% 1.71/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.61    inference(nnf_transformation,[],[f4])).
% 1.71/0.61  fof(f4,axiom,(
% 1.71/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.71/0.61  fof(f817,plain,(
% 1.71/0.61    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(backward_demodulation,[],[f738,f249])).
% 1.71/0.61  fof(f249,plain,(
% 1.71/0.61    k1_xboole_0 = sK1 | ~spl8_5),
% 1.71/0.61    inference(avatar_component_clause,[],[f247])).
% 1.71/0.61  fof(f247,plain,(
% 1.71/0.61    spl8_5 <=> k1_xboole_0 = sK1),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.71/0.61  fof(f738,plain,(
% 1.71/0.61    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_6),
% 1.71/0.61    inference(backward_demodulation,[],[f84,f255])).
% 1.71/0.61  fof(f255,plain,(
% 1.71/0.61    k1_xboole_0 = sK2 | ~spl8_6),
% 1.71/0.61    inference(avatar_component_clause,[],[f253])).
% 1.71/0.61  fof(f253,plain,(
% 1.71/0.61    spl8_6 <=> k1_xboole_0 = sK2),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.71/0.61  fof(f84,plain,(
% 1.71/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.61    inference(cnf_transformation,[],[f70])).
% 1.71/0.61  fof(f70,plain,(
% 1.71/0.61    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.71/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f69])).
% 1.71/0.61  fof(f69,plain,(
% 1.71/0.61    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f36,plain,(
% 1.71/0.61    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.71/0.61    inference(flattening,[],[f35])).
% 1.71/0.61  fof(f35,plain,(
% 1.71/0.61    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.71/0.61    inference(ennf_transformation,[],[f33])).
% 1.71/0.61  fof(f33,negated_conjecture,(
% 1.71/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.71/0.61    inference(negated_conjecture,[],[f32])).
% 1.71/0.61  fof(f32,conjecture,(
% 1.71/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.71/0.61  fof(f1304,plain,(
% 1.71/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_11 | ~spl8_24 | ~spl8_25)),
% 1.71/0.61    inference(forward_demodulation,[],[f1297,f155])).
% 1.71/0.61  fof(f1297,plain,(
% 1.71/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_11 | ~spl8_24 | ~spl8_25)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f736,f729,f1003,f891,f158])).
% 1.71/0.61  fof(f158,plain,(
% 1.71/0.61    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.61    inference(equality_resolution,[],[f140])).
% 1.71/0.61  fof(f140,plain,(
% 1.71/0.61    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f68])).
% 1.71/0.61  fof(f68,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.71/0.61    inference(flattening,[],[f67])).
% 1.71/0.61  fof(f67,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.71/0.61    inference(ennf_transformation,[],[f31])).
% 1.71/0.61  fof(f31,axiom,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.71/0.61  fof(f891,plain,(
% 1.71/0.61    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_5 | ~spl8_6 | ~spl8_24)),
% 1.71/0.61    inference(backward_demodulation,[],[f826,f880])).
% 1.71/0.61  fof(f880,plain,(
% 1.71/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_6 | ~spl8_24)),
% 1.71/0.61    inference(backward_demodulation,[],[f750,f879])).
% 1.71/0.61  fof(f879,plain,(
% 1.71/0.61    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl8_6 | ~spl8_24)),
% 1.71/0.61    inference(forward_demodulation,[],[f717,f255])).
% 1.71/0.61  fof(f717,plain,(
% 1.71/0.61    k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | ~spl8_24),
% 1.71/0.61    inference(avatar_component_clause,[],[f716])).
% 1.71/0.61  fof(f716,plain,(
% 1.71/0.61    spl8_24 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.71/0.61  fof(f750,plain,(
% 1.71/0.61    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl8_6),
% 1.71/0.61    inference(backward_demodulation,[],[f207,f255])).
% 1.71/0.61  fof(f207,plain,(
% 1.71/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f85,f82,f184,f112])).
% 1.71/0.61  fof(f112,plain,(
% 1.71/0.61    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f48])).
% 1.71/0.61  fof(f48,plain,(
% 1.71/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(flattening,[],[f47])).
% 1.71/0.61  fof(f47,plain,(
% 1.71/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.61    inference(ennf_transformation,[],[f21])).
% 1.71/0.61  fof(f21,axiom,(
% 1.71/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.71/0.61  fof(f184,plain,(
% 1.71/0.61    v1_relat_1(sK2)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f84,f130])).
% 1.71/0.61  fof(f130,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f59])).
% 1.71/0.61  fof(f59,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f23])).
% 1.71/0.61  fof(f23,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.71/0.61  fof(f82,plain,(
% 1.71/0.61    v1_funct_1(sK2)),
% 1.71/0.61    inference(cnf_transformation,[],[f70])).
% 1.71/0.61  fof(f85,plain,(
% 1.71/0.61    v2_funct_1(sK2)),
% 1.71/0.61    inference(cnf_transformation,[],[f70])).
% 1.71/0.61  fof(f826,plain,(
% 1.71/0.61    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(backward_demodulation,[],[f755,f249])).
% 1.71/0.61  fof(f755,plain,(
% 1.71/0.61    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1) | ~spl8_6),
% 1.71/0.61    inference(backward_demodulation,[],[f220,f255])).
% 1.71/0.61  fof(f220,plain,(
% 1.71/0.61    v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 1.71/0.61    inference(forward_demodulation,[],[f202,f189])).
% 1.71/0.61  fof(f189,plain,(
% 1.71/0.61    sK1 = k2_relat_1(sK2)),
% 1.71/0.61    inference(forward_demodulation,[],[f185,f86])).
% 1.71/0.61  fof(f86,plain,(
% 1.71/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.71/0.61    inference(cnf_transformation,[],[f70])).
% 1.71/0.61  fof(f185,plain,(
% 1.71/0.61    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f84,f131])).
% 1.71/0.61  fof(f131,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f60])).
% 1.71/0.61  fof(f60,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f25])).
% 1.71/0.61  fof(f25,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.71/0.61  fof(f202,plain,(
% 1.71/0.61    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f82,f184,f107])).
% 1.71/0.61  fof(f107,plain,(
% 1.71/0.61    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f44])).
% 1.71/0.61  fof(f44,plain,(
% 1.71/0.61    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(flattening,[],[f43])).
% 1.71/0.61  fof(f43,plain,(
% 1.71/0.61    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.61    inference(ennf_transformation,[],[f30])).
% 1.71/0.61  fof(f30,axiom,(
% 1.71/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.71/0.61  fof(f1003,plain,(
% 1.71/0.61    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_11)),
% 1.71/0.61    inference(forward_demodulation,[],[f918,f940])).
% 1.71/0.61  fof(f940,plain,(
% 1.71/0.61    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl8_5 | ~spl8_6 | ~spl8_11)),
% 1.71/0.61    inference(forward_demodulation,[],[f939,f255])).
% 1.71/0.61  fof(f939,plain,(
% 1.71/0.61    k1_xboole_0 = k2_funct_1(sK2) | (~spl8_5 | ~spl8_11)),
% 1.71/0.61    inference(forward_demodulation,[],[f938,f143])).
% 1.71/0.61  fof(f143,plain,(
% 1.71/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.71/0.61    inference(definition_unfolding,[],[f89,f90])).
% 1.71/0.61  fof(f90,plain,(
% 1.71/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f29])).
% 1.71/0.61  fof(f29,axiom,(
% 1.71/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.71/0.61  fof(f89,plain,(
% 1.71/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.71/0.61    inference(cnf_transformation,[],[f14])).
% 1.71/0.61  fof(f14,axiom,(
% 1.71/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.71/0.61  fof(f938,plain,(
% 1.71/0.61    k2_funct_1(sK2) = k6_partfun1(k1_xboole_0) | (~spl8_5 | ~spl8_11)),
% 1.71/0.61    inference(forward_demodulation,[],[f421,f249])).
% 1.71/0.61  fof(f421,plain,(
% 1.71/0.61    k2_funct_1(sK2) = k6_partfun1(sK1) | ~spl8_11),
% 1.71/0.61    inference(avatar_component_clause,[],[f419])).
% 1.71/0.61  fof(f419,plain,(
% 1.71/0.61    spl8_11 <=> k2_funct_1(sK2) = k6_partfun1(sK1)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.71/0.61  fof(f918,plain,(
% 1.71/0.61    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl8_2 | ~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(forward_demodulation,[],[f917,f255])).
% 1.71/0.61  fof(f917,plain,(
% 1.71/0.61    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl8_2 | ~spl8_5)),
% 1.71/0.61    inference(forward_demodulation,[],[f175,f249])).
% 1.71/0.61  fof(f175,plain,(
% 1.71/0.61    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl8_2),
% 1.71/0.61    inference(avatar_component_clause,[],[f173])).
% 1.71/0.61  fof(f173,plain,(
% 1.71/0.61    spl8_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.71/0.61  fof(f729,plain,(
% 1.71/0.61    r1_tarski(k1_xboole_0,sK0) | ~spl8_25),
% 1.71/0.61    inference(avatar_component_clause,[],[f727])).
% 1.71/0.61  fof(f727,plain,(
% 1.71/0.61    spl8_25 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.71/0.61  fof(f736,plain,(
% 1.71/0.61    v1_funct_1(k1_xboole_0) | ~spl8_6),
% 1.71/0.61    inference(backward_demodulation,[],[f82,f255])).
% 1.71/0.61  fof(f900,plain,(
% 1.71/0.61    ~spl8_6 | spl8_12 | ~spl8_24),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f899])).
% 1.71/0.61  fof(f899,plain,(
% 1.71/0.61    $false | (~spl8_6 | spl8_12 | ~spl8_24)),
% 1.71/0.61    inference(subsumption_resolution,[],[f887,f143])).
% 1.71/0.61  fof(f887,plain,(
% 1.71/0.61    k1_xboole_0 != k6_partfun1(k1_xboole_0) | (~spl8_6 | spl8_12 | ~spl8_24)),
% 1.71/0.61    inference(backward_demodulation,[],[f783,f880])).
% 1.71/0.61  fof(f783,plain,(
% 1.71/0.61    k1_xboole_0 != k6_partfun1(k1_relat_1(k1_xboole_0)) | (~spl8_6 | spl8_12)),
% 1.71/0.61    inference(backward_demodulation,[],[f425,f255])).
% 1.71/0.61  fof(f425,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | spl8_12),
% 1.71/0.61    inference(avatar_component_clause,[],[f423])).
% 1.71/0.61  fof(f423,plain,(
% 1.71/0.61    spl8_12 <=> sK2 = k6_partfun1(k1_relat_1(sK2))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.71/0.61  fof(f861,plain,(
% 1.71/0.61    ~spl8_1 | spl8_3 | ~spl8_5 | ~spl8_6),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f860])).
% 1.71/0.61  fof(f860,plain,(
% 1.71/0.61    $false | (~spl8_1 | spl8_3 | ~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(subsumption_resolution,[],[f859,f855])).
% 1.71/0.61  fof(f855,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl8_3 | ~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(forward_demodulation,[],[f820,f156])).
% 1.71/0.61  fof(f156,plain,(
% 1.71/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.71/0.61    inference(equality_resolution,[],[f128])).
% 1.71/0.61  fof(f128,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.71/0.61    inference(cnf_transformation,[],[f81])).
% 1.71/0.61  fof(f820,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl8_3 | ~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(backward_demodulation,[],[f743,f249])).
% 1.71/0.61  fof(f743,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl8_3 | ~spl8_6)),
% 1.71/0.61    inference(backward_demodulation,[],[f179,f255])).
% 1.71/0.61  fof(f179,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl8_3),
% 1.71/0.61    inference(avatar_component_clause,[],[f177])).
% 1.71/0.61  fof(f177,plain,(
% 1.71/0.61    spl8_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.71/0.61  fof(f859,plain,(
% 1.71/0.61    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl8_1 | ~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(forward_demodulation,[],[f832,f156])).
% 1.71/0.61  fof(f832,plain,(
% 1.71/0.61    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) | (~spl8_1 | ~spl8_5 | ~spl8_6)),
% 1.71/0.61    inference(backward_demodulation,[],[f769,f249])).
% 1.71/0.61  fof(f769,plain,(
% 1.71/0.61    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) | (~spl8_1 | ~spl8_6)),
% 1.71/0.61    inference(backward_demodulation,[],[f287,f255])).
% 1.71/0.61  fof(f287,plain,(
% 1.71/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl8_1),
% 1.71/0.61    inference(forward_demodulation,[],[f286,f218])).
% 1.71/0.61  fof(f218,plain,(
% 1.71/0.61    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(forward_demodulation,[],[f206,f189])).
% 1.71/0.61  fof(f206,plain,(
% 1.71/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f85,f82,f184,f111])).
% 1.71/0.61  fof(f111,plain,(
% 1.71/0.61    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f48])).
% 1.71/0.61  fof(f286,plain,(
% 1.71/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~spl8_1),
% 1.71/0.61    inference(forward_demodulation,[],[f272,f207])).
% 1.71/0.61  fof(f272,plain,(
% 1.71/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl8_1),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f170,f204,f108])).
% 1.71/0.61  fof(f108,plain,(
% 1.71/0.61    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f44])).
% 1.71/0.61  fof(f204,plain,(
% 1.71/0.61    v1_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f82,f184,f109])).
% 1.71/0.61  fof(f109,plain,(
% 1.71/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f46])).
% 1.71/0.61  fof(f46,plain,(
% 1.71/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(flattening,[],[f45])).
% 1.71/0.61  fof(f45,plain,(
% 1.71/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.61    inference(ennf_transformation,[],[f15])).
% 1.71/0.61  fof(f15,axiom,(
% 1.71/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.71/0.61  fof(f170,plain,(
% 1.71/0.61    v1_funct_1(k2_funct_1(sK2)) | ~spl8_1),
% 1.71/0.61    inference(avatar_component_clause,[],[f169])).
% 1.71/0.61  fof(f169,plain,(
% 1.71/0.61    spl8_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.71/0.61  fof(f730,plain,(
% 1.71/0.61    spl8_25 | ~spl8_5),
% 1.71/0.61    inference(avatar_split_clause,[],[f313,f247,f727])).
% 1.71/0.61  fof(f313,plain,(
% 1.71/0.61    k1_xboole_0 != sK1 | r1_tarski(k1_xboole_0,sK0)),
% 1.71/0.61    inference(forward_demodulation,[],[f312,f189])).
% 1.71/0.61  fof(f312,plain,(
% 1.71/0.61    r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(sK2)),
% 1.71/0.61    inference(subsumption_resolution,[],[f311,f184])).
% 1.71/0.61  fof(f311,plain,(
% 1.71/0.61    r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(superposition,[],[f225,f105])).
% 1.71/0.61  fof(f105,plain,(
% 1.71/0.61    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f71])).
% 1.71/0.61  fof(f71,plain,(
% 1.71/0.61    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(nnf_transformation,[],[f42])).
% 1.71/0.61  fof(f42,plain,(
% 1.71/0.61    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(ennf_transformation,[],[f11])).
% 1.71/0.61  fof(f11,axiom,(
% 1.71/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.71/0.61  fof(f225,plain,(
% 1.71/0.61    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f184,f186,f116])).
% 1.71/0.61  fof(f116,plain,(
% 1.71/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f72])).
% 1.71/0.61  fof(f72,plain,(
% 1.71/0.61    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.71/0.61    inference(nnf_transformation,[],[f55])).
% 1.71/0.61  fof(f55,plain,(
% 1.71/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.71/0.61    inference(ennf_transformation,[],[f7])).
% 1.71/0.61  fof(f7,axiom,(
% 1.71/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.71/0.61  fof(f186,plain,(
% 1.71/0.61    v4_relat_1(sK2,sK0)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f84,f132])).
% 1.71/0.61  fof(f132,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f61])).
% 1.71/0.61  fof(f61,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f34])).
% 1.71/0.61  fof(f34,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.71/0.61    inference(pure_predicate_removal,[],[f24])).
% 1.71/0.61  fof(f24,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.61  fof(f721,plain,(
% 1.71/0.61    spl8_24 | ~spl8_5),
% 1.71/0.61    inference(avatar_split_clause,[],[f720,f247,f716])).
% 1.71/0.61  fof(f720,plain,(
% 1.71/0.61    k1_xboole_0 != sK1 | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(subsumption_resolution,[],[f329,f204])).
% 1.71/0.61  fof(f329,plain,(
% 1.71/0.61    k1_xboole_0 != sK1 | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(superposition,[],[f104,f218])).
% 1.71/0.61  fof(f104,plain,(
% 1.71/0.61    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f71])).
% 1.71/0.61  fof(f628,plain,(
% 1.71/0.61    ~spl8_1 | spl8_3 | spl8_4),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f627])).
% 1.71/0.61  fof(f627,plain,(
% 1.71/0.61    $false | (~spl8_1 | spl8_3 | spl8_4)),
% 1.71/0.61    inference(subsumption_resolution,[],[f624,f287])).
% 1.71/0.61  fof(f624,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl8_1 | spl8_3 | spl8_4)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f170,f225,f245,f289,f179,f141])).
% 1.71/0.61  fof(f141,plain,(
% 1.71/0.61    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f68])).
% 1.71/0.61  fof(f289,plain,(
% 1.71/0.61    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl8_1),
% 1.71/0.61    inference(forward_demodulation,[],[f288,f218])).
% 1.71/0.61  fof(f288,plain,(
% 1.71/0.61    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~spl8_1),
% 1.71/0.61    inference(forward_demodulation,[],[f271,f207])).
% 1.71/0.61  fof(f271,plain,(
% 1.71/0.61    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl8_1),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f170,f204,f107])).
% 1.71/0.61  fof(f245,plain,(
% 1.71/0.61    k1_xboole_0 != k1_relat_1(sK2) | spl8_4),
% 1.71/0.61    inference(avatar_component_clause,[],[f243])).
% 1.71/0.61  fof(f243,plain,(
% 1.71/0.61    spl8_4 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.71/0.61  fof(f614,plain,(
% 1.71/0.61    ~spl8_1 | spl8_2 | spl8_4),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f613])).
% 1.71/0.61  fof(f613,plain,(
% 1.71/0.61    $false | (~spl8_1 | spl8_2 | spl8_4)),
% 1.71/0.61    inference(subsumption_resolution,[],[f610,f287])).
% 1.71/0.61  fof(f610,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl8_1 | spl8_2 | spl8_4)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f170,f225,f175,f245,f289,f139])).
% 1.71/0.61  fof(f139,plain,(
% 1.71/0.61    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f68])).
% 1.71/0.61  fof(f426,plain,(
% 1.71/0.61    spl8_11 | ~spl8_12),
% 1.71/0.61    inference(avatar_split_clause,[],[f417,f423,f419])).
% 1.71/0.61  fof(f417,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1)),
% 1.71/0.61    inference(subsumption_resolution,[],[f416,f189])).
% 1.71/0.61  fof(f416,plain,(
% 1.71/0.61    sK1 != k2_relat_1(sK2) | sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1)),
% 1.71/0.61    inference(forward_demodulation,[],[f415,f149])).
% 1.71/0.61  fof(f149,plain,(
% 1.71/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.71/0.61    inference(definition_unfolding,[],[f97,f90])).
% 1.71/0.61  fof(f97,plain,(
% 1.71/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.71/0.61    inference(cnf_transformation,[],[f12])).
% 1.71/0.61  fof(f12,axiom,(
% 1.71/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.71/0.61  fof(f415,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1))),
% 1.71/0.61    inference(subsumption_resolution,[],[f414,f184])).
% 1.71/0.61  fof(f414,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(subsumption_resolution,[],[f413,f82])).
% 1.71/0.61  fof(f413,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(subsumption_resolution,[],[f412,f147])).
% 1.71/0.61  fof(f147,plain,(
% 1.71/0.61    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.71/0.61    inference(definition_unfolding,[],[f93,f90])).
% 1.71/0.61  fof(f93,plain,(
% 1.71/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f16])).
% 1.71/0.61  fof(f16,axiom,(
% 1.71/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.71/0.61  fof(f412,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(subsumption_resolution,[],[f411,f146])).
% 1.71/0.61  fof(f146,plain,(
% 1.71/0.61    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.71/0.61    inference(definition_unfolding,[],[f94,f90])).
% 1.71/0.61  fof(f94,plain,(
% 1.71/0.61    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f16])).
% 1.71/0.61  fof(f411,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(k6_partfun1(sK1)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(subsumption_resolution,[],[f409,f85])).
% 1.71/0.61  fof(f409,plain,(
% 1.71/0.61    sK2 != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = k6_partfun1(sK1) | k2_relat_1(sK2) != k1_relat_1(k6_partfun1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(k6_partfun1(sK1)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(superposition,[],[f152,f215])).
% 1.71/0.61  fof(f215,plain,(
% 1.71/0.61    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 1.71/0.61    inference(forward_demodulation,[],[f214,f189])).
% 1.71/0.61  fof(f214,plain,(
% 1.71/0.61    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f184,f150])).
% 1.71/0.61  fof(f150,plain,(
% 1.71/0.61    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f101,f90])).
% 1.71/0.61  fof(f101,plain,(
% 1.71/0.61    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f39])).
% 1.71/0.61  fof(f39,plain,(
% 1.71/0.61    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.71/0.61    inference(ennf_transformation,[],[f13])).
% 1.71/0.61  fof(f13,axiom,(
% 1.71/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.71/0.61  fof(f152,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f115,f90])).
% 1.71/0.61  fof(f115,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f54])).
% 1.71/0.61  fof(f54,plain,(
% 1.71/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(flattening,[],[f53])).
% 1.71/0.61  fof(f53,plain,(
% 1.71/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.61    inference(ennf_transformation,[],[f22])).
% 1.71/0.61  fof(f22,axiom,(
% 1.71/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 1.71/0.61  fof(f258,plain,(
% 1.71/0.61    ~spl8_4 | spl8_5),
% 1.71/0.61    inference(avatar_split_clause,[],[f257,f247,f243])).
% 1.71/0.61  fof(f257,plain,(
% 1.71/0.61    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2)),
% 1.71/0.61    inference(subsumption_resolution,[],[f233,f184])).
% 1.71/0.61  fof(f233,plain,(
% 1.71/0.61    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(superposition,[],[f104,f189])).
% 1.71/0.61  fof(f256,plain,(
% 1.71/0.61    spl8_6 | ~spl8_5),
% 1.71/0.61    inference(avatar_split_clause,[],[f251,f247,f253])).
% 1.71/0.61  fof(f251,plain,(
% 1.71/0.61    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 1.71/0.61    inference(subsumption_resolution,[],[f232,f184])).
% 1.71/0.61  fof(f232,plain,(
% 1.71/0.61    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.71/0.61    inference(superposition,[],[f103,f189])).
% 1.71/0.61  fof(f103,plain,(
% 1.71/0.61    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f41])).
% 1.71/0.61  fof(f41,plain,(
% 1.71/0.61    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(flattening,[],[f40])).
% 1.71/0.61  fof(f40,plain,(
% 1.71/0.61    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(ennf_transformation,[],[f10])).
% 1.71/0.61  fof(f10,axiom,(
% 1.71/0.61    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.71/0.61  fof(f191,plain,(
% 1.71/0.61    spl8_1),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f190])).
% 1.71/0.61  fof(f190,plain,(
% 1.71/0.61    $false | spl8_1),
% 1.71/0.61    inference(subsumption_resolution,[],[f184,f181])).
% 1.71/0.61  fof(f181,plain,(
% 1.71/0.61    ~v1_relat_1(sK2) | spl8_1),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f82,f171,f110])).
% 1.71/0.61  fof(f110,plain,(
% 1.71/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f46])).
% 1.71/0.61  fof(f171,plain,(
% 1.71/0.61    ~v1_funct_1(k2_funct_1(sK2)) | spl8_1),
% 1.71/0.61    inference(avatar_component_clause,[],[f169])).
% 1.71/0.61  fof(f180,plain,(
% 1.71/0.61    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.71/0.61    inference(avatar_split_clause,[],[f87,f177,f173,f169])).
% 1.71/0.61  fof(f87,plain,(
% 1.71/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.71/0.61    inference(cnf_transformation,[],[f70])).
% 1.71/0.61  % SZS output end Proof for theBenchmark
% 1.71/0.61  % (5040)------------------------------
% 1.71/0.61  % (5040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (5040)Termination reason: Refutation
% 1.71/0.61  
% 1.71/0.61  % (5040)Memory used [KB]: 11257
% 1.71/0.61  % (5040)Time elapsed: 0.193 s
% 1.71/0.61  % (5040)------------------------------
% 1.71/0.61  % (5040)------------------------------
% 1.71/0.62  % (5036)Refutation not found, incomplete strategy% (5036)------------------------------
% 1.71/0.62  % (5036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.62  % (5036)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.62  
% 1.71/0.62  % (5036)Memory used [KB]: 11513
% 1.71/0.62  % (5036)Time elapsed: 0.178 s
% 1.71/0.62  % (5036)------------------------------
% 1.71/0.62  % (5036)------------------------------
% 2.05/0.64  % (5013)Success in time 0.271 s
%------------------------------------------------------------------------------
