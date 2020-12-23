%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:59 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  193 (1076 expanded)
%              Number of leaves         :   25 ( 337 expanded)
%              Depth                    :   22
%              Number of atoms          :  721 (10239 expanded)
%              Number of equality atoms :  204 (3460 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f305,f367,f771,f1086])).

fof(f1086,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f1085])).

fof(f1085,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1082,f145])).

fof(f145,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f64,f143])).

fof(f143,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f142,f120])).

fof(f120,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f84])).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f142,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f140,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f64,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f1082,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f769,f1062])).

fof(f1062,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f138,f1057])).

fof(f1057,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1056,f99])).

fof(f99,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f65])).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1056,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1055,f941])).

fof(f941,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f304,f811])).

fof(f811,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f810,f121])).

fof(f121,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f118,f84])).

fof(f118,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f78,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f810,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f805,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f805,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f294,f81])).

fof(f294,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl4_2
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f304,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl4_3
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1055,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k4_relat_1(sK3)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f807,f811])).

fof(f807,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f806,f121])).

fof(f806,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f803,f56])).

fof(f803,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f294,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f138,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f102,f121])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f74,f65])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f769,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f759,f383])).

fof(f383,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f371,f256])).

fof(f256,plain,(
    sK0 = k2_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f122,f252])).

fof(f252,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f250,f99])).

fof(f250,plain,(
    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f173,f249])).

fof(f249,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f248,f143])).

fof(f248,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f247,f53])).

fof(f247,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f246,f54])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f246,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f245,f55])).

fof(f245,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f244,f61])).

fof(f244,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f243,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f243,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f85,f59])).

fof(f59,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f173,plain,(
    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k4_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f172,f143])).

fof(f172,plain,(
    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f171,f120])).

fof(f171,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f169,f53])).

fof(f169,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f61])).

fof(f122,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f120,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f371,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2))))
    | ~ spl4_4 ),
    inference(resolution,[],[f353,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f353,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl4_4
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f759,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f389,f724])).

fof(f724,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f718,f723])).

fof(f723,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f705,f202])).

fof(f202,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f92,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f705,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f60,f536])).

fof(f536,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f533,f53])).

fof(f533,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f213,f55])).

fof(f213,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f210,f56])).

fof(f210,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f94,f58])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f718,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f717,f53])).

fof(f717,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f716,f55])).

fof(f716,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f715,f56])).

fof(f715,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f707,f58])).

fof(f707,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f96,f536])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f389,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f379,f266])).

fof(f266,plain,(
    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f265,f143])).

fof(f265,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f264,f53])).

fof(f264,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f263,f54])).

fof(f263,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f262,f55])).

fof(f262,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f261,f61])).

fof(f261,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f260,f63])).

fof(f260,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f86,f59])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f379,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f353,f320])).

fof(f320,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(X9,sK2),sK3) = k5_relat_1(X9,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f181,f120])).

fof(f181,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k5_relat_1(k5_relat_1(X15,X16),sK3) = k5_relat_1(X15,k5_relat_1(X16,sK3))
      | ~ v1_relat_1(X15) ) ),
    inference(resolution,[],[f77,f121])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f771,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f770])).

fof(f770,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f765,f97])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f765,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_2 ),
    inference(backward_demodulation,[],[f714,f724])).

fof(f714,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f713,f56])).

fof(f713,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f712,f57])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f712,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f711,f58])).

fof(f711,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f710,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f710,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f706,f295])).

fof(f295,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f293])).

fof(f706,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f336,f536])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | v2_funct_1(X1)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f335,f53])).

fof(f335,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f334,f54])).

fof(f334,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v2_funct_1(X1)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_funct_2(X1,sK1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f333,f55])).

fof(f333,plain,(
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
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,(
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
    inference(superposition,[],[f90,f59])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f367,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f365,f120])).

fof(f365,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(resolution,[],[f354,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f354,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f352])).

fof(f305,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f300,f293,f302])).

fof(f300,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f299,f56])).

fof(f299,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f298,f57])).

fof(f298,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f297,f58])).

fof(f297,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f282,f62])).

fof(f282,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f85,f279])).

fof(f279,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f278,f56])).

fof(f278,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f277,f57])).

fof(f277,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f276,f58])).

fof(f276,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f275,f53])).

fof(f275,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f274,f54])).

fof(f274,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f273,f55])).

fof(f273,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f87,f60])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:29:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (15169)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.50  % (15161)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (15152)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (15159)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (15177)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15149)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (15148)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (15157)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (15158)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (15170)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (15162)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (15175)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (15155)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (15153)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (15171)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (15154)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (15173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (15163)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (15174)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (15151)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (15150)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (15164)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (15168)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (15176)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (15164)Refutation not found, incomplete strategy% (15164)------------------------------
% 0.22/0.55  % (15164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15164)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15164)Memory used [KB]: 10746
% 0.22/0.55  % (15164)Time elapsed: 0.140 s
% 0.22/0.55  % (15164)------------------------------
% 0.22/0.55  % (15164)------------------------------
% 0.22/0.55  % (15156)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (15165)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (15160)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (15166)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (15167)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.57  % (15172)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.69/0.61  % (15154)Refutation found. Thanks to Tanya!
% 1.69/0.61  % SZS status Theorem for theBenchmark
% 1.69/0.61  % SZS output start Proof for theBenchmark
% 1.69/0.61  fof(f1087,plain,(
% 1.69/0.61    $false),
% 1.69/0.61    inference(avatar_sat_refutation,[],[f305,f367,f771,f1086])).
% 1.69/0.61  fof(f1086,plain,(
% 1.69/0.61    ~spl4_2 | ~spl4_3 | ~spl4_4),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f1085])).
% 1.69/0.61  fof(f1085,plain,(
% 1.69/0.61    $false | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.69/0.61    inference(subsumption_resolution,[],[f1082,f145])).
% 1.69/0.61  fof(f145,plain,(
% 1.69/0.61    sK3 != k4_relat_1(sK2)),
% 1.69/0.61    inference(superposition,[],[f64,f143])).
% 1.69/0.61  fof(f143,plain,(
% 1.69/0.61    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f142,f120])).
% 1.69/0.61  fof(f120,plain,(
% 1.69/0.61    v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f117,f84])).
% 1.69/0.61  fof(f84,plain,(
% 1.69/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f3])).
% 1.69/0.61  fof(f3,axiom,(
% 1.69/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.69/0.61  fof(f117,plain,(
% 1.69/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.69/0.61    inference(resolution,[],[f78,f55])).
% 1.69/0.61  fof(f55,plain,(
% 1.69/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f51,plain,(
% 1.69/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f50,f49])).
% 1.69/0.61  fof(f49,plain,(
% 1.69/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f50,plain,(
% 1.69/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f24,plain,(
% 1.69/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.69/0.61    inference(flattening,[],[f23])).
% 1.69/0.61  fof(f23,plain,(
% 1.69/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.69/0.61    inference(ennf_transformation,[],[f22])).
% 1.69/0.61  fof(f22,negated_conjecture,(
% 1.69/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.69/0.61    inference(negated_conjecture,[],[f21])).
% 1.69/0.61  fof(f21,conjecture,(
% 1.69/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.69/0.61  fof(f78,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f30])).
% 1.69/0.61  fof(f30,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f1])).
% 1.69/0.61  fof(f1,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.69/0.61  fof(f142,plain,(
% 1.69/0.61    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f140,f53])).
% 1.69/0.61  fof(f53,plain,(
% 1.69/0.61    v1_funct_1(sK2)),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f140,plain,(
% 1.69/0.61    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(resolution,[],[f81,f61])).
% 1.69/0.61  fof(f61,plain,(
% 1.69/0.61    v2_funct_1(sK2)),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f81,plain,(
% 1.69/0.61    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f34])).
% 1.69/0.61  fof(f34,plain,(
% 1.69/0.61    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f33])).
% 1.69/0.61  fof(f33,plain,(
% 1.69/0.61    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f9])).
% 1.69/0.61  fof(f9,axiom,(
% 1.69/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.69/0.61  fof(f64,plain,(
% 1.69/0.61    k2_funct_1(sK2) != sK3),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f1082,plain,(
% 1.69/0.61    sK3 = k4_relat_1(sK2) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.69/0.61    inference(backward_demodulation,[],[f769,f1062])).
% 1.69/0.61  fof(f1062,plain,(
% 1.69/0.61    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl4_2 | ~spl4_3)),
% 1.69/0.61    inference(backward_demodulation,[],[f138,f1057])).
% 1.69/0.61  fof(f1057,plain,(
% 1.69/0.61    sK1 = k1_relat_1(sK3) | (~spl4_2 | ~spl4_3)),
% 1.69/0.61    inference(forward_demodulation,[],[f1056,f99])).
% 1.69/0.61  fof(f99,plain,(
% 1.69/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.69/0.61    inference(definition_unfolding,[],[f71,f65])).
% 1.69/0.61  fof(f65,plain,(
% 1.69/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f17])).
% 1.69/0.61  fof(f17,axiom,(
% 1.69/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.69/0.61  fof(f71,plain,(
% 1.69/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.61    inference(cnf_transformation,[],[f6])).
% 1.69/0.61  fof(f6,axiom,(
% 1.69/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.69/0.61  fof(f1056,plain,(
% 1.69/0.61    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | (~spl4_2 | ~spl4_3)),
% 1.69/0.61    inference(forward_demodulation,[],[f1055,f941])).
% 1.69/0.61  fof(f941,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) | (~spl4_2 | ~spl4_3)),
% 1.69/0.61    inference(forward_demodulation,[],[f304,f811])).
% 1.69/0.61  fof(f811,plain,(
% 1.69/0.61    k4_relat_1(sK3) = k2_funct_1(sK3) | ~spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f810,f121])).
% 1.69/0.61  fof(f121,plain,(
% 1.69/0.61    v1_relat_1(sK3)),
% 1.69/0.61    inference(subsumption_resolution,[],[f118,f84])).
% 1.69/0.61  fof(f118,plain,(
% 1.69/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.69/0.61    inference(resolution,[],[f78,f58])).
% 1.69/0.61  fof(f58,plain,(
% 1.69/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f810,plain,(
% 1.69/0.61    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f805,f56])).
% 1.69/0.61  fof(f56,plain,(
% 1.69/0.61    v1_funct_1(sK3)),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f805,plain,(
% 1.69/0.61    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.69/0.61    inference(resolution,[],[f294,f81])).
% 1.69/0.61  fof(f294,plain,(
% 1.69/0.61    v2_funct_1(sK3) | ~spl4_2),
% 1.69/0.61    inference(avatar_component_clause,[],[f293])).
% 1.69/0.61  fof(f293,plain,(
% 1.69/0.61    spl4_2 <=> v2_funct_1(sK3)),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.69/0.61  fof(f304,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_3),
% 1.69/0.61    inference(avatar_component_clause,[],[f302])).
% 1.69/0.61  fof(f302,plain,(
% 1.69/0.61    spl4_3 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.69/0.61  fof(f1055,plain,(
% 1.69/0.61    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))) | ~spl4_2),
% 1.69/0.61    inference(forward_demodulation,[],[f807,f811])).
% 1.69/0.61  fof(f807,plain,(
% 1.69/0.61    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f806,f121])).
% 1.69/0.61  fof(f806,plain,(
% 1.69/0.61    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f803,f56])).
% 1.69/0.61  fof(f803,plain,(
% 1.69/0.61    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.69/0.61    inference(resolution,[],[f294,f83])).
% 1.69/0.61  fof(f83,plain,(
% 1.69/0.61    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f36,plain,(
% 1.69/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f35])).
% 1.69/0.61  fof(f35,plain,(
% 1.69/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f12])).
% 1.69/0.61  fof(f12,axiom,(
% 1.69/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 1.69/0.61  fof(f138,plain,(
% 1.69/0.61    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.69/0.61    inference(resolution,[],[f102,f121])).
% 1.69/0.61  fof(f102,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.69/0.61    inference(definition_unfolding,[],[f74,f65])).
% 1.69/0.61  fof(f74,plain,(
% 1.69/0.61    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f27])).
% 1.69/0.61  fof(f27,plain,(
% 1.69/0.61    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f7])).
% 1.69/0.61  fof(f7,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.69/0.61  fof(f769,plain,(
% 1.69/0.61    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_4),
% 1.69/0.61    inference(forward_demodulation,[],[f759,f383])).
% 1.69/0.61  fof(f383,plain,(
% 1.69/0.61    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) | ~spl4_4),
% 1.69/0.61    inference(forward_demodulation,[],[f371,f256])).
% 1.69/0.61  fof(f256,plain,(
% 1.69/0.61    sK0 = k2_relat_1(k4_relat_1(sK2))),
% 1.69/0.61    inference(backward_demodulation,[],[f122,f252])).
% 1.69/0.61  fof(f252,plain,(
% 1.69/0.61    sK0 = k1_relat_1(sK2)),
% 1.69/0.61    inference(forward_demodulation,[],[f250,f99])).
% 1.69/0.61  fof(f250,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))),
% 1.69/0.61    inference(backward_demodulation,[],[f173,f249])).
% 1.69/0.61  fof(f249,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))),
% 1.69/0.61    inference(forward_demodulation,[],[f248,f143])).
% 1.69/0.61  fof(f248,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.61    inference(subsumption_resolution,[],[f247,f53])).
% 1.69/0.61  fof(f247,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f246,f54])).
% 1.69/0.61  fof(f54,plain,(
% 1.69/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f246,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f245,f55])).
% 1.69/0.61  fof(f245,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f244,f61])).
% 1.69/0.61  fof(f244,plain,(
% 1.69/0.61    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f243,f63])).
% 1.69/0.61  fof(f63,plain,(
% 1.69/0.61    k1_xboole_0 != sK1),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f243,plain,(
% 1.69/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(trivial_inequality_removal,[],[f242])).
% 1.69/0.61  fof(f242,plain,(
% 1.69/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(superposition,[],[f85,f59])).
% 1.69/0.61  fof(f59,plain,(
% 1.69/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f85,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f38])).
% 1.69/0.61  fof(f38,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.61    inference(flattening,[],[f37])).
% 1.69/0.61  fof(f37,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.61    inference(ennf_transformation,[],[f20])).
% 1.69/0.61  fof(f20,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.69/0.61  fof(f173,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k4_relat_1(sK2)))),
% 1.69/0.61    inference(forward_demodulation,[],[f172,f143])).
% 1.69/0.61  fof(f172,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.69/0.61    inference(subsumption_resolution,[],[f171,f120])).
% 1.69/0.61  fof(f171,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f169,f53])).
% 1.69/0.61  fof(f169,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(resolution,[],[f83,f61])).
% 1.69/0.61  fof(f122,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 1.69/0.61    inference(resolution,[],[f120,f76])).
% 1.69/0.61  fof(f76,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f28])).
% 1.69/0.61  fof(f28,plain,(
% 1.69/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f4])).
% 1.69/0.61  fof(f4,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.69/0.61  fof(f371,plain,(
% 1.69/0.61    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) | ~spl4_4),
% 1.69/0.61    inference(resolution,[],[f353,f101])).
% 1.69/0.61  fof(f101,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.69/0.61    inference(definition_unfolding,[],[f73,f65])).
% 1.69/0.61  fof(f73,plain,(
% 1.69/0.61    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f26])).
% 1.69/0.61  fof(f26,plain,(
% 1.69/0.61    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f8])).
% 1.69/0.61  fof(f8,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.69/0.61  fof(f353,plain,(
% 1.69/0.61    v1_relat_1(k4_relat_1(sK2)) | ~spl4_4),
% 1.69/0.61    inference(avatar_component_clause,[],[f352])).
% 1.69/0.61  fof(f352,plain,(
% 1.69/0.61    spl4_4 <=> v1_relat_1(k4_relat_1(sK2))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.69/0.61  fof(f759,plain,(
% 1.69/0.61    k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_4),
% 1.69/0.61    inference(backward_demodulation,[],[f389,f724])).
% 1.69/0.61  fof(f724,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.69/0.61    inference(global_subsumption,[],[f718,f723])).
% 1.69/0.61  fof(f723,plain,(
% 1.69/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.61    inference(resolution,[],[f705,f202])).
% 1.69/0.61  fof(f202,plain,(
% 1.69/0.61    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.69/0.61    inference(resolution,[],[f92,f69])).
% 1.69/0.61  fof(f69,plain,(
% 1.69/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f15])).
% 1.69/0.61  fof(f15,axiom,(
% 1.69/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.69/0.61  fof(f92,plain,(
% 1.69/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f52])).
% 1.69/0.61  fof(f52,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(nnf_transformation,[],[f44])).
% 1.69/0.61  fof(f44,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(flattening,[],[f43])).
% 1.69/0.61  fof(f43,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.69/0.61    inference(ennf_transformation,[],[f13])).
% 1.69/0.61  fof(f13,axiom,(
% 1.69/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.69/0.61  fof(f705,plain,(
% 1.69/0.61    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.69/0.61    inference(backward_demodulation,[],[f60,f536])).
% 1.69/0.61  fof(f536,plain,(
% 1.69/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.69/0.61    inference(subsumption_resolution,[],[f533,f53])).
% 1.69/0.61  fof(f533,plain,(
% 1.69/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(resolution,[],[f213,f55])).
% 1.69/0.61  fof(f213,plain,(
% 1.69/0.61    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f210,f56])).
% 1.69/0.61  fof(f210,plain,(
% 1.69/0.61    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.69/0.61    inference(resolution,[],[f94,f58])).
% 1.69/0.61  fof(f94,plain,(
% 1.69/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f46])).
% 1.69/0.61  fof(f46,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.61    inference(flattening,[],[f45])).
% 1.69/0.61  fof(f45,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.61    inference(ennf_transformation,[],[f16])).
% 1.69/0.61  fof(f16,axiom,(
% 1.69/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.69/0.61  fof(f60,plain,(
% 1.69/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f718,plain,(
% 1.69/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.61    inference(subsumption_resolution,[],[f717,f53])).
% 1.69/0.61  fof(f717,plain,(
% 1.69/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f716,f55])).
% 1.69/0.61  fof(f716,plain,(
% 1.69/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f715,f56])).
% 1.69/0.61  fof(f715,plain,(
% 1.69/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f707,f58])).
% 1.69/0.61  fof(f707,plain,(
% 1.69/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(superposition,[],[f96,f536])).
% 1.69/0.61  fof(f96,plain,(
% 1.69/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f48])).
% 1.69/0.61  fof(f48,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.61    inference(flattening,[],[f47])).
% 1.69/0.61  fof(f47,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.61    inference(ennf_transformation,[],[f14])).
% 1.69/0.61  fof(f14,axiom,(
% 1.69/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.69/0.61  fof(f389,plain,(
% 1.69/0.61    k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_4),
% 1.69/0.61    inference(forward_demodulation,[],[f379,f266])).
% 1.69/0.61  fof(f266,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 1.69/0.61    inference(forward_demodulation,[],[f265,f143])).
% 1.69/0.61  fof(f265,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f264,f53])).
% 1.69/0.61  fof(f264,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f263,f54])).
% 1.69/0.61  fof(f263,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f262,f55])).
% 1.69/0.61  fof(f262,plain,(
% 1.69/0.61    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f261,f61])).
% 1.69/0.61  fof(f261,plain,(
% 1.69/0.61    ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f260,f63])).
% 1.69/0.61  fof(f260,plain,(
% 1.69/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(trivial_inequality_removal,[],[f259])).
% 1.69/0.61  fof(f259,plain,(
% 1.69/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(superposition,[],[f86,f59])).
% 1.69/0.61  fof(f86,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f38])).
% 1.69/0.61  fof(f379,plain,(
% 1.69/0.61    k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) | ~spl4_4),
% 1.69/0.61    inference(resolution,[],[f353,f320])).
% 1.69/0.61  fof(f320,plain,(
% 1.69/0.61    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(X9,sK2),sK3) = k5_relat_1(X9,k5_relat_1(sK2,sK3))) )),
% 1.69/0.61    inference(resolution,[],[f181,f120])).
% 1.69/0.61  fof(f181,plain,(
% 1.69/0.61    ( ! [X15,X16] : (~v1_relat_1(X16) | k5_relat_1(k5_relat_1(X15,X16),sK3) = k5_relat_1(X15,k5_relat_1(X16,sK3)) | ~v1_relat_1(X15)) )),
% 1.69/0.61    inference(resolution,[],[f77,f121])).
% 1.69/0.61  fof(f77,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f29])).
% 1.69/0.61  fof(f29,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f5])).
% 1.69/0.61  fof(f5,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.69/0.61  fof(f771,plain,(
% 1.69/0.61    spl4_2),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f770])).
% 1.69/0.61  fof(f770,plain,(
% 1.69/0.61    $false | spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f765,f97])).
% 1.69/0.61  fof(f97,plain,(
% 1.69/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.69/0.61    inference(definition_unfolding,[],[f67,f65])).
% 1.69/0.61  fof(f67,plain,(
% 1.69/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f11])).
% 1.69/0.61  fof(f11,axiom,(
% 1.69/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.69/0.61  fof(f765,plain,(
% 1.69/0.61    ~v2_funct_1(k6_partfun1(sK0)) | spl4_2),
% 1.69/0.61    inference(backward_demodulation,[],[f714,f724])).
% 1.69/0.61  fof(f714,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f713,f56])).
% 1.69/0.61  fof(f713,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f712,f57])).
% 1.69/0.61  fof(f57,plain,(
% 1.69/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f712,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f711,f58])).
% 1.69/0.61  fof(f711,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f710,f62])).
% 1.69/0.61  fof(f62,plain,(
% 1.69/0.61    k1_xboole_0 != sK0),
% 1.69/0.61    inference(cnf_transformation,[],[f51])).
% 1.69/0.61  fof(f710,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl4_2),
% 1.69/0.61    inference(subsumption_resolution,[],[f706,f295])).
% 1.69/0.61  fof(f295,plain,(
% 1.69/0.61    ~v2_funct_1(sK3) | spl4_2),
% 1.69/0.61    inference(avatar_component_clause,[],[f293])).
% 1.69/0.61  fof(f706,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.69/0.61    inference(superposition,[],[f336,f536])).
% 1.69/0.61  fof(f336,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f335,f53])).
% 1.69/0.61  fof(f335,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f334,f54])).
% 1.69/0.61  fof(f334,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f333,f55])).
% 1.69/0.61  fof(f333,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.69/0.61    inference(trivial_inequality_removal,[],[f330])).
% 1.69/0.61  fof(f330,plain,(
% 1.69/0.61    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.69/0.61    inference(superposition,[],[f90,f59])).
% 1.69/0.61  fof(f90,plain,(
% 1.69/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f42])).
% 1.69/0.61  fof(f42,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.69/0.61    inference(flattening,[],[f41])).
% 1.69/0.61  fof(f41,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.69/0.61    inference(ennf_transformation,[],[f19])).
% 2.04/0.63  fof(f19,axiom,(
% 2.04/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.04/0.63  fof(f367,plain,(
% 2.04/0.63    spl4_4),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f366])).
% 2.04/0.63  fof(f366,plain,(
% 2.04/0.63    $false | spl4_4),
% 2.04/0.63    inference(subsumption_resolution,[],[f365,f120])).
% 2.04/0.63  fof(f365,plain,(
% 2.04/0.63    ~v1_relat_1(sK2) | spl4_4),
% 2.04/0.63    inference(resolution,[],[f354,f72])).
% 2.04/0.63  fof(f72,plain,(
% 2.04/0.63    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f25])).
% 2.04/0.63  fof(f25,plain,(
% 2.04/0.63    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f2])).
% 2.04/0.63  fof(f2,axiom,(
% 2.04/0.63    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.04/0.63  fof(f354,plain,(
% 2.04/0.63    ~v1_relat_1(k4_relat_1(sK2)) | spl4_4),
% 2.04/0.63    inference(avatar_component_clause,[],[f352])).
% 2.04/0.63  fof(f305,plain,(
% 2.04/0.63    spl4_3 | ~spl4_2),
% 2.04/0.63    inference(avatar_split_clause,[],[f300,f293,f302])).
% 2.04/0.63  fof(f300,plain,(
% 2.04/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.04/0.63    inference(subsumption_resolution,[],[f299,f56])).
% 2.04/0.63  fof(f299,plain,(
% 2.04/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f298,f57])).
% 2.04/0.63  fof(f298,plain,(
% 2.04/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f297,f58])).
% 2.04/0.63  fof(f297,plain,(
% 2.04/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f282,f62])).
% 2.04/0.63  fof(f282,plain,(
% 2.04/0.63    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(trivial_inequality_removal,[],[f281])).
% 2.04/0.63  fof(f281,plain,(
% 2.04/0.63    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(superposition,[],[f85,f279])).
% 2.04/0.63  fof(f279,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f278,f56])).
% 2.04/0.63  fof(f278,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f277,f57])).
% 2.04/0.63  fof(f277,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f276,f58])).
% 2.04/0.63  fof(f276,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f275,f53])).
% 2.04/0.63  fof(f275,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f274,f54])).
% 2.04/0.63  fof(f274,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f273,f55])).
% 2.04/0.63  fof(f273,plain,(
% 2.04/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.04/0.63    inference(resolution,[],[f87,f60])).
% 2.04/0.63  fof(f87,plain,(
% 2.04/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f40])).
% 2.04/0.63  fof(f40,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.04/0.63    inference(flattening,[],[f39])).
% 2.04/0.63  fof(f39,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.04/0.63    inference(ennf_transformation,[],[f18])).
% 2.04/0.63  fof(f18,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.04/0.63  % SZS output end Proof for theBenchmark
% 2.04/0.63  % (15154)------------------------------
% 2.04/0.63  % (15154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (15154)Termination reason: Refutation
% 2.04/0.63  
% 2.04/0.63  % (15154)Memory used [KB]: 11897
% 2.04/0.63  % (15154)Time elapsed: 0.149 s
% 2.04/0.63  % (15154)------------------------------
% 2.04/0.63  % (15154)------------------------------
% 2.04/0.63  % (15147)Success in time 0.271 s
%------------------------------------------------------------------------------
