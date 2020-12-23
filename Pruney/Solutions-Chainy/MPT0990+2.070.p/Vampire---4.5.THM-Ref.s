%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:40 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  190 (1043 expanded)
%              Number of leaves         :   24 ( 326 expanded)
%              Depth                    :   22
%              Number of atoms          :  712 (10152 expanded)
%              Number of equality atoms :  204 (3464 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1070,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f289,f348,f748,f1069])).

fof(f1069,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f1068])).

fof(f1068,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1065,f137])).

fof(f137,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f63,f135])).

fof(f135,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f113])).

fof(f113,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f49,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f134,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f132,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f132,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f63,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f1065,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f746,f1045])).

fof(f1045,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f130,f1022])).

fof(f1022,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1021,f97])).

fof(f97,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1021,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1020,f901])).

fof(f901,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f288,f775])).

fof(f775,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f774,f114])).

fof(f114,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f774,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f769,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f769,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f278,f78])).

fof(f278,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl4_2
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f288,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl4_3
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1020,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k4_relat_1(sK3)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f771,f775])).

fof(f771,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f770,f114])).

fof(f770,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f767,f55])).

fof(f767,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f278,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f130,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f100,f114])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f72,f64])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f746,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f737,f364])).

fof(f364,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f352,f240])).

fof(f240,plain,(
    sK0 = k2_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f116,f236])).

fof(f236,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f234,f97])).

fof(f234,plain,(
    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f156,f233])).

fof(f233,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f232,f135])).

fof(f232,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f231,f52])).

fof(f231,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f230,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f230,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f229,f54])).

fof(f229,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f228,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f227,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f227,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f82,f58])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f156,plain,(
    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k4_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f155,f135])).

fof(f155,plain,(
    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f154,f113])).

fof(f154,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f52])).

fof(f152,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f60])).

fof(f116,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f113,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f352,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2))))
    | ~ spl4_4 ),
    inference(resolution,[],[f334,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f71,f64])).

fof(f71,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f334,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl4_4
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f737,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f370,f686])).

fof(f686,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f680,f685])).

fof(f685,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f667,f190])).

fof(f190,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f89,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f667,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f59,f501])).

fof(f501,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f498,f52])).

fof(f498,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f201,f54])).

fof(f201,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f198,f55])).

fof(f198,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f91,f57])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f59,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f680,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f679,f52])).

fof(f679,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f678,f54])).

fof(f678,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f677,f55])).

fof(f677,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f669,f57])).

fof(f669,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f93,f501])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f370,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f360,f250])).

fof(f250,plain,(
    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f249,f135])).

fof(f249,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f248,f52])).

fof(f248,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f247,f53])).

fof(f247,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f246,f54])).

fof(f246,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f245,f60])).

fof(f245,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f244,f62])).

fof(f244,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f243])).

fof(f243,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f83,f58])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f360,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f334,f293])).

fof(f293,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k5_relat_1(k5_relat_1(X6,sK2),sK3) = k5_relat_1(X6,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f171,f113])).

fof(f171,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(k5_relat_1(X11,X12),sK3) = k5_relat_1(X11,k5_relat_1(X12,sK3))
      | ~ v1_relat_1(X11) ) ),
    inference(resolution,[],[f75,f114])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f748,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f742,f95])).

fof(f95,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f742,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_2 ),
    inference(backward_demodulation,[],[f676,f686])).

fof(f676,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f675,f55])).

fof(f675,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f674,f56])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f674,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f673,f57])).

fof(f673,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f672,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f672,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f668,f279])).

fof(f279,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f277])).

fof(f668,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f318,f501])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | v2_funct_1(X1)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f317,f52])).

fof(f317,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f316,f53])).

fof(f316,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f315,f54])).

fof(f315,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f312])).

fof(f312,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f87,f58])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f348,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f346,f113])).

fof(f346,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(resolution,[],[f335,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f335,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f333])).

fof(f289,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f284,f277,f286])).

fof(f284,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f283,f55])).

fof(f283,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f282,f56])).

fof(f282,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f281,f57])).

fof(f281,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f266,f61])).

fof(f266,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f82,f263])).

fof(f263,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f262,f55])).

fof(f262,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f261,f56])).

fof(f261,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f260,f57])).

fof(f260,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f259,f52])).

fof(f259,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f258,f53])).

fof(f258,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f257,f54])).

fof(f257,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f84,f59])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (10146)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (10161)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (10170)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (10154)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (10147)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (10153)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (10162)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (10149)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (10148)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (10168)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (10162)Refutation not found, incomplete strategy% (10162)------------------------------
% 0.22/0.54  % (10162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10160)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (10162)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10162)Memory used [KB]: 10746
% 0.22/0.54  % (10162)Time elapsed: 0.119 s
% 0.22/0.54  % (10162)------------------------------
% 0.22/0.54  % (10162)------------------------------
% 0.22/0.54  % (10167)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (10151)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (10157)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (10152)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (10171)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (10150)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (10173)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (10156)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (10175)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (10172)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (10166)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (10155)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (10169)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (10159)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (10174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (10164)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (10165)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (10163)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (10158)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.91/0.64  % (10152)Refutation found. Thanks to Tanya!
% 1.91/0.64  % SZS status Theorem for theBenchmark
% 1.91/0.64  % SZS output start Proof for theBenchmark
% 1.91/0.64  fof(f1070,plain,(
% 1.91/0.64    $false),
% 1.91/0.64    inference(avatar_sat_refutation,[],[f289,f348,f748,f1069])).
% 1.91/0.64  fof(f1069,plain,(
% 1.91/0.64    ~spl4_2 | ~spl4_3 | ~spl4_4),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f1068])).
% 1.91/0.64  fof(f1068,plain,(
% 1.91/0.64    $false | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.91/0.64    inference(subsumption_resolution,[],[f1065,f137])).
% 1.91/0.64  fof(f137,plain,(
% 1.91/0.64    sK3 != k4_relat_1(sK2)),
% 1.91/0.64    inference(superposition,[],[f63,f135])).
% 1.91/0.64  fof(f135,plain,(
% 1.91/0.64    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f134,f113])).
% 1.91/0.64  fof(f113,plain,(
% 1.91/0.64    v1_relat_1(sK2)),
% 1.91/0.64    inference(resolution,[],[f81,f54])).
% 1.91/0.64  fof(f54,plain,(
% 1.91/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f50,plain,(
% 1.91/0.64    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.91/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f49,f48])).
% 1.91/0.64  fof(f48,plain,(
% 1.91/0.64    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.91/0.64    introduced(choice_axiom,[])).
% 1.91/0.64  fof(f49,plain,(
% 1.91/0.64    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.91/0.64    introduced(choice_axiom,[])).
% 1.91/0.64  fof(f23,plain,(
% 1.91/0.64    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.91/0.64    inference(flattening,[],[f22])).
% 1.91/0.64  fof(f22,plain,(
% 1.91/0.64    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.91/0.64    inference(ennf_transformation,[],[f21])).
% 1.91/0.64  fof(f21,negated_conjecture,(
% 1.91/0.64    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.91/0.64    inference(negated_conjecture,[],[f20])).
% 1.91/0.64  fof(f20,conjecture,(
% 1.91/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.91/0.64  fof(f81,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f35])).
% 1.91/0.64  fof(f35,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(ennf_transformation,[],[f11])).
% 1.91/0.64  fof(f11,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.91/0.64  fof(f134,plain,(
% 1.91/0.64    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f132,f52])).
% 1.91/0.64  fof(f52,plain,(
% 1.91/0.64    v1_funct_1(sK2)),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f132,plain,(
% 1.91/0.64    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.91/0.64    inference(resolution,[],[f78,f60])).
% 1.91/0.64  fof(f60,plain,(
% 1.91/0.64    v2_funct_1(sK2)),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f78,plain,(
% 1.91/0.64    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f32])).
% 1.91/0.64  fof(f32,plain,(
% 1.91/0.64    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.64    inference(flattening,[],[f31])).
% 1.91/0.64  fof(f31,plain,(
% 1.91/0.64    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.64    inference(ennf_transformation,[],[f7])).
% 1.91/0.64  fof(f7,axiom,(
% 1.91/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.91/0.64  fof(f63,plain,(
% 1.91/0.64    k2_funct_1(sK2) != sK3),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f1065,plain,(
% 1.91/0.64    sK3 = k4_relat_1(sK2) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.91/0.64    inference(backward_demodulation,[],[f746,f1045])).
% 1.91/0.64  fof(f1045,plain,(
% 1.91/0.64    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl4_2 | ~spl4_3)),
% 1.91/0.64    inference(backward_demodulation,[],[f130,f1022])).
% 1.91/0.64  fof(f1022,plain,(
% 1.91/0.64    sK1 = k1_relat_1(sK3) | (~spl4_2 | ~spl4_3)),
% 1.91/0.64    inference(forward_demodulation,[],[f1021,f97])).
% 1.91/0.64  fof(f97,plain,(
% 1.91/0.64    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.91/0.64    inference(definition_unfolding,[],[f69,f64])).
% 1.91/0.64  fof(f64,plain,(
% 1.91/0.64    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f16])).
% 1.91/0.64  fof(f16,axiom,(
% 1.91/0.64    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.91/0.64  fof(f69,plain,(
% 1.91/0.64    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.91/0.64    inference(cnf_transformation,[],[f4])).
% 1.91/0.64  fof(f4,axiom,(
% 1.91/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.91/0.64  fof(f1021,plain,(
% 1.91/0.64    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | (~spl4_2 | ~spl4_3)),
% 1.91/0.64    inference(forward_demodulation,[],[f1020,f901])).
% 1.91/0.64  fof(f901,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) | (~spl4_2 | ~spl4_3)),
% 1.91/0.64    inference(forward_demodulation,[],[f288,f775])).
% 1.91/0.64  fof(f775,plain,(
% 1.91/0.64    k4_relat_1(sK3) = k2_funct_1(sK3) | ~spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f774,f114])).
% 1.91/0.64  fof(f114,plain,(
% 1.91/0.64    v1_relat_1(sK3)),
% 1.91/0.64    inference(resolution,[],[f81,f57])).
% 1.91/0.64  fof(f57,plain,(
% 1.91/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f774,plain,(
% 1.91/0.64    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f769,f55])).
% 1.91/0.64  fof(f55,plain,(
% 1.91/0.64    v1_funct_1(sK3)),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f769,plain,(
% 1.91/0.64    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.91/0.64    inference(resolution,[],[f278,f78])).
% 1.91/0.64  fof(f278,plain,(
% 1.91/0.64    v2_funct_1(sK3) | ~spl4_2),
% 1.91/0.64    inference(avatar_component_clause,[],[f277])).
% 1.91/0.64  fof(f277,plain,(
% 1.91/0.64    spl4_2 <=> v2_funct_1(sK3)),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.91/0.64  fof(f288,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_3),
% 1.91/0.64    inference(avatar_component_clause,[],[f286])).
% 1.91/0.64  fof(f286,plain,(
% 1.91/0.64    spl4_3 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.91/0.64  fof(f1020,plain,(
% 1.91/0.64    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))) | ~spl4_2),
% 1.91/0.64    inference(forward_demodulation,[],[f771,f775])).
% 1.91/0.64  fof(f771,plain,(
% 1.91/0.64    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f770,f114])).
% 1.91/0.64  fof(f770,plain,(
% 1.91/0.64    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f767,f55])).
% 1.91/0.64  fof(f767,plain,(
% 1.91/0.64    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.91/0.64    inference(resolution,[],[f278,f80])).
% 1.91/0.64  fof(f80,plain,(
% 1.91/0.64    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f34])).
% 1.91/0.64  fof(f34,plain,(
% 1.91/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.64    inference(flattening,[],[f33])).
% 1.91/0.64  fof(f33,plain,(
% 1.91/0.64    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.64    inference(ennf_transformation,[],[f10])).
% 1.91/0.64  fof(f10,axiom,(
% 1.91/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 1.91/0.64  fof(f130,plain,(
% 1.91/0.64    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.91/0.64    inference(resolution,[],[f100,f114])).
% 1.91/0.64  fof(f100,plain,(
% 1.91/0.64    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.91/0.64    inference(definition_unfolding,[],[f72,f64])).
% 1.91/0.64  fof(f72,plain,(
% 1.91/0.64    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f26])).
% 1.91/0.64  fof(f26,plain,(
% 1.91/0.64    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.91/0.64    inference(ennf_transformation,[],[f5])).
% 1.91/0.64  fof(f5,axiom,(
% 1.91/0.64    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.91/0.64  fof(f746,plain,(
% 1.91/0.64    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_4),
% 1.91/0.64    inference(forward_demodulation,[],[f737,f364])).
% 1.91/0.64  fof(f364,plain,(
% 1.91/0.64    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) | ~spl4_4),
% 1.91/0.64    inference(forward_demodulation,[],[f352,f240])).
% 1.91/0.64  fof(f240,plain,(
% 1.91/0.64    sK0 = k2_relat_1(k4_relat_1(sK2))),
% 1.91/0.64    inference(backward_demodulation,[],[f116,f236])).
% 1.91/0.64  fof(f236,plain,(
% 1.91/0.64    sK0 = k1_relat_1(sK2)),
% 1.91/0.64    inference(forward_demodulation,[],[f234,f97])).
% 1.91/0.64  fof(f234,plain,(
% 1.91/0.64    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))),
% 1.91/0.64    inference(backward_demodulation,[],[f156,f233])).
% 1.91/0.64  fof(f233,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))),
% 1.91/0.64    inference(forward_demodulation,[],[f232,f135])).
% 1.91/0.64  fof(f232,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.91/0.64    inference(subsumption_resolution,[],[f231,f52])).
% 1.91/0.64  fof(f231,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f230,f53])).
% 1.91/0.64  fof(f53,plain,(
% 1.91/0.64    v1_funct_2(sK2,sK0,sK1)),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f230,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f229,f54])).
% 1.91/0.64  fof(f229,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f228,f60])).
% 1.91/0.64  fof(f228,plain,(
% 1.91/0.64    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f227,f62])).
% 1.91/0.64  fof(f62,plain,(
% 1.91/0.64    k1_xboole_0 != sK1),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f227,plain,(
% 1.91/0.64    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(trivial_inequality_removal,[],[f226])).
% 1.91/0.64  fof(f226,plain,(
% 1.91/0.64    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(superposition,[],[f82,f58])).
% 1.91/0.64  fof(f58,plain,(
% 1.91/0.64    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f82,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f37])).
% 1.91/0.64  fof(f37,plain,(
% 1.91/0.64    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.64    inference(flattening,[],[f36])).
% 1.91/0.64  fof(f36,plain,(
% 1.91/0.64    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.64    inference(ennf_transformation,[],[f19])).
% 1.91/0.64  fof(f19,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.91/0.64  fof(f156,plain,(
% 1.91/0.64    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k4_relat_1(sK2)))),
% 1.91/0.64    inference(forward_demodulation,[],[f155,f135])).
% 1.91/0.64  fof(f155,plain,(
% 1.91/0.64    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.91/0.64    inference(subsumption_resolution,[],[f154,f113])).
% 1.91/0.64  fof(f154,plain,(
% 1.91/0.64    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f152,f52])).
% 1.91/0.64  fof(f152,plain,(
% 1.91/0.64    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.91/0.64    inference(resolution,[],[f80,f60])).
% 1.91/0.64  fof(f116,plain,(
% 1.91/0.64    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 1.91/0.64    inference(resolution,[],[f113,f74])).
% 1.91/0.64  fof(f74,plain,(
% 1.91/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.91/0.64    inference(cnf_transformation,[],[f27])).
% 1.91/0.64  fof(f27,plain,(
% 1.91/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.91/0.64    inference(ennf_transformation,[],[f2])).
% 1.91/0.64  fof(f2,axiom,(
% 1.91/0.64    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.91/0.64  fof(f352,plain,(
% 1.91/0.64    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) | ~spl4_4),
% 1.91/0.64    inference(resolution,[],[f334,f99])).
% 1.91/0.64  fof(f99,plain,(
% 1.91/0.64    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.91/0.64    inference(definition_unfolding,[],[f71,f64])).
% 1.91/0.64  fof(f71,plain,(
% 1.91/0.64    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f25])).
% 1.91/0.64  fof(f25,plain,(
% 1.91/0.64    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.91/0.64    inference(ennf_transformation,[],[f6])).
% 1.91/0.64  fof(f6,axiom,(
% 1.91/0.64    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.91/0.64  fof(f334,plain,(
% 1.91/0.64    v1_relat_1(k4_relat_1(sK2)) | ~spl4_4),
% 1.91/0.64    inference(avatar_component_clause,[],[f333])).
% 1.91/0.64  fof(f333,plain,(
% 1.91/0.64    spl4_4 <=> v1_relat_1(k4_relat_1(sK2))),
% 1.91/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.91/0.64  fof(f737,plain,(
% 1.91/0.64    k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_4),
% 1.91/0.64    inference(backward_demodulation,[],[f370,f686])).
% 1.91/0.64  fof(f686,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.91/0.64    inference(global_subsumption,[],[f680,f685])).
% 1.91/0.64  fof(f685,plain,(
% 1.91/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.91/0.64    inference(resolution,[],[f667,f190])).
% 1.91/0.64  fof(f190,plain,(
% 1.91/0.64    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.91/0.64    inference(resolution,[],[f89,f94])).
% 1.91/0.64  fof(f94,plain,(
% 1.91/0.64    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.91/0.64    inference(definition_unfolding,[],[f65,f64])).
% 1.91/0.64  fof(f65,plain,(
% 1.91/0.64    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.91/0.64    inference(cnf_transformation,[],[f13])).
% 1.91/0.64  fof(f13,axiom,(
% 1.91/0.64    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.91/0.64  fof(f89,plain,(
% 1.91/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.64    inference(cnf_transformation,[],[f51])).
% 1.91/0.64  fof(f51,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(nnf_transformation,[],[f43])).
% 1.91/0.64  fof(f43,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.64    inference(flattening,[],[f42])).
% 1.91/0.64  fof(f42,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.91/0.64    inference(ennf_transformation,[],[f12])).
% 1.91/0.64  fof(f12,axiom,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.91/0.64  fof(f667,plain,(
% 1.91/0.64    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.91/0.64    inference(backward_demodulation,[],[f59,f501])).
% 1.91/0.64  fof(f501,plain,(
% 1.91/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f498,f52])).
% 1.91/0.64  fof(f498,plain,(
% 1.91/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(resolution,[],[f201,f54])).
% 1.91/0.64  fof(f201,plain,(
% 1.91/0.64    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f198,f55])).
% 1.91/0.64  fof(f198,plain,(
% 1.91/0.64    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.91/0.64    inference(resolution,[],[f91,f57])).
% 1.91/0.64  fof(f91,plain,(
% 1.91/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f45])).
% 1.91/0.64  fof(f45,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.91/0.64    inference(flattening,[],[f44])).
% 1.91/0.64  fof(f44,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.91/0.64    inference(ennf_transformation,[],[f15])).
% 1.91/0.64  fof(f15,axiom,(
% 1.91/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.91/0.64  fof(f59,plain,(
% 1.91/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f680,plain,(
% 1.91/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.91/0.64    inference(subsumption_resolution,[],[f679,f52])).
% 1.91/0.64  fof(f679,plain,(
% 1.91/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f678,f54])).
% 1.91/0.64  fof(f678,plain,(
% 1.91/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f677,f55])).
% 1.91/0.64  fof(f677,plain,(
% 1.91/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f669,f57])).
% 1.91/0.64  fof(f669,plain,(
% 1.91/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(superposition,[],[f93,f501])).
% 1.91/0.64  fof(f93,plain,(
% 1.91/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f47])).
% 1.91/0.64  fof(f47,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.91/0.64    inference(flattening,[],[f46])).
% 1.91/0.64  fof(f46,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.91/0.64    inference(ennf_transformation,[],[f14])).
% 1.91/0.64  fof(f14,axiom,(
% 1.91/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.91/0.64  fof(f370,plain,(
% 1.91/0.64    k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_4),
% 1.91/0.64    inference(forward_demodulation,[],[f360,f250])).
% 1.91/0.64  fof(f250,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 1.91/0.64    inference(forward_demodulation,[],[f249,f135])).
% 1.91/0.64  fof(f249,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f248,f52])).
% 1.91/0.64  fof(f248,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f247,f53])).
% 1.91/0.64  fof(f247,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f246,f54])).
% 1.91/0.64  fof(f246,plain,(
% 1.91/0.64    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f245,f60])).
% 1.91/0.64  fof(f245,plain,(
% 1.91/0.64    ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(subsumption_resolution,[],[f244,f62])).
% 1.91/0.64  fof(f244,plain,(
% 1.91/0.64    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(trivial_inequality_removal,[],[f243])).
% 1.91/0.64  fof(f243,plain,(
% 1.91/0.64    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.91/0.64    inference(superposition,[],[f83,f58])).
% 1.91/0.64  fof(f83,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f37])).
% 1.91/0.64  fof(f360,plain,(
% 1.91/0.64    k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) | ~spl4_4),
% 1.91/0.64    inference(resolution,[],[f334,f293])).
% 1.91/0.64  fof(f293,plain,(
% 1.91/0.64    ( ! [X6] : (~v1_relat_1(X6) | k5_relat_1(k5_relat_1(X6,sK2),sK3) = k5_relat_1(X6,k5_relat_1(sK2,sK3))) )),
% 1.91/0.64    inference(resolution,[],[f171,f113])).
% 1.91/0.64  fof(f171,plain,(
% 1.91/0.64    ( ! [X12,X11] : (~v1_relat_1(X12) | k5_relat_1(k5_relat_1(X11,X12),sK3) = k5_relat_1(X11,k5_relat_1(X12,sK3)) | ~v1_relat_1(X11)) )),
% 1.91/0.64    inference(resolution,[],[f75,f114])).
% 1.91/0.64  fof(f75,plain,(
% 1.91/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f28])).
% 1.91/0.64  fof(f28,plain,(
% 1.91/0.64    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.91/0.64    inference(ennf_transformation,[],[f3])).
% 1.91/0.64  fof(f3,axiom,(
% 1.91/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.91/0.64  fof(f748,plain,(
% 1.91/0.64    spl4_2),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f747])).
% 1.91/0.64  fof(f747,plain,(
% 1.91/0.64    $false | spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f742,f95])).
% 1.91/0.64  fof(f95,plain,(
% 1.91/0.64    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.91/0.64    inference(definition_unfolding,[],[f67,f64])).
% 1.91/0.64  fof(f67,plain,(
% 1.91/0.64    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.91/0.64    inference(cnf_transformation,[],[f9])).
% 1.91/0.64  fof(f9,axiom,(
% 1.91/0.64    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.91/0.64  fof(f742,plain,(
% 1.91/0.64    ~v2_funct_1(k6_partfun1(sK0)) | spl4_2),
% 1.91/0.64    inference(backward_demodulation,[],[f676,f686])).
% 1.91/0.64  fof(f676,plain,(
% 1.91/0.64    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f675,f55])).
% 1.91/0.64  fof(f675,plain,(
% 1.91/0.64    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f674,f56])).
% 1.91/0.64  fof(f56,plain,(
% 1.91/0.64    v1_funct_2(sK3,sK1,sK0)),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f674,plain,(
% 1.91/0.64    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f673,f57])).
% 1.91/0.64  fof(f673,plain,(
% 1.91/0.64    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f672,f61])).
% 1.91/0.64  fof(f61,plain,(
% 1.91/0.64    k1_xboole_0 != sK0),
% 1.91/0.64    inference(cnf_transformation,[],[f50])).
% 1.91/0.64  fof(f672,plain,(
% 1.91/0.64    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_2),
% 1.91/0.64    inference(subsumption_resolution,[],[f668,f279])).
% 1.91/0.64  fof(f279,plain,(
% 1.91/0.64    ~v2_funct_1(sK3) | spl4_2),
% 1.91/0.64    inference(avatar_component_clause,[],[f277])).
% 1.91/0.64  fof(f668,plain,(
% 1.91/0.64    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(superposition,[],[f318,f501])).
% 1.91/0.64  fof(f318,plain,(
% 1.91/0.64    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f317,f52])).
% 1.91/0.64  fof(f317,plain,(
% 1.91/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f316,f53])).
% 1.91/0.64  fof(f316,plain,(
% 1.91/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.91/0.64    inference(subsumption_resolution,[],[f315,f54])).
% 1.91/0.64  fof(f315,plain,(
% 1.91/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.91/0.64    inference(trivial_inequality_removal,[],[f312])).
% 1.91/0.64  fof(f312,plain,(
% 1.91/0.64    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.91/0.64    inference(superposition,[],[f87,f58])).
% 1.91/0.64  fof(f87,plain,(
% 1.91/0.64    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f41])).
% 1.91/0.64  fof(f41,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.91/0.64    inference(flattening,[],[f40])).
% 1.91/0.64  fof(f40,plain,(
% 1.91/0.64    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.91/0.64    inference(ennf_transformation,[],[f18])).
% 1.91/0.64  fof(f18,axiom,(
% 1.91/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.91/0.64  fof(f348,plain,(
% 1.91/0.64    spl4_4),
% 1.91/0.64    inference(avatar_contradiction_clause,[],[f347])).
% 1.91/0.64  fof(f347,plain,(
% 1.91/0.64    $false | spl4_4),
% 1.91/0.64    inference(subsumption_resolution,[],[f346,f113])).
% 1.91/0.64  fof(f346,plain,(
% 1.91/0.64    ~v1_relat_1(sK2) | spl4_4),
% 1.91/0.64    inference(resolution,[],[f335,f70])).
% 1.91/0.64  fof(f70,plain,(
% 1.91/0.64    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f24])).
% 1.91/0.64  fof(f24,plain,(
% 1.91/0.64    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.91/0.64    inference(ennf_transformation,[],[f1])).
% 1.91/0.64  fof(f1,axiom,(
% 1.91/0.64    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.91/0.64  fof(f335,plain,(
% 1.91/0.64    ~v1_relat_1(k4_relat_1(sK2)) | spl4_4),
% 1.91/0.64    inference(avatar_component_clause,[],[f333])).
% 1.91/0.64  fof(f289,plain,(
% 1.91/0.64    spl4_3 | ~spl4_2),
% 1.91/0.64    inference(avatar_split_clause,[],[f284,f277,f286])).
% 1.91/0.64  fof(f284,plain,(
% 1.91/0.64    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.91/0.64    inference(subsumption_resolution,[],[f283,f55])).
% 1.91/0.64  fof(f283,plain,(
% 1.91/0.64    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f282,f56])).
% 1.91/0.64  fof(f282,plain,(
% 1.91/0.64    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f281,f57])).
% 1.91/0.64  fof(f281,plain,(
% 1.91/0.64    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f266,f61])).
% 1.91/0.64  fof(f266,plain,(
% 1.91/0.64    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(trivial_inequality_removal,[],[f265])).
% 1.91/0.64  fof(f265,plain,(
% 1.91/0.64    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(superposition,[],[f82,f263])).
% 1.91/0.64  fof(f263,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f262,f55])).
% 1.91/0.64  fof(f262,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f261,f56])).
% 1.91/0.64  fof(f261,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f260,f57])).
% 1.91/0.64  fof(f260,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f259,f52])).
% 1.91/0.64  fof(f259,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f258,f53])).
% 1.91/0.64  fof(f258,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(subsumption_resolution,[],[f257,f54])).
% 1.91/0.64  fof(f257,plain,(
% 1.91/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.91/0.64    inference(resolution,[],[f84,f59])).
% 1.91/0.64  fof(f84,plain,(
% 1.91/0.64    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.91/0.64    inference(cnf_transformation,[],[f39])).
% 1.91/0.64  fof(f39,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.64    inference(flattening,[],[f38])).
% 1.91/0.64  fof(f38,plain,(
% 1.91/0.64    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.64    inference(ennf_transformation,[],[f17])).
% 1.91/0.64  fof(f17,axiom,(
% 1.91/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.91/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.91/0.64  % SZS output end Proof for theBenchmark
% 1.91/0.64  % (10152)------------------------------
% 1.91/0.64  % (10152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.64  % (10152)Termination reason: Refutation
% 1.91/0.64  
% 1.91/0.64  % (10152)Memory used [KB]: 11769
% 1.91/0.64  % (10152)Time elapsed: 0.183 s
% 1.91/0.64  % (10152)------------------------------
% 1.91/0.64  % (10152)------------------------------
% 2.06/0.64  % (10145)Success in time 0.273 s
%------------------------------------------------------------------------------
