%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 403 expanded)
%              Number of leaves         :   27 ( 119 expanded)
%              Depth                    :   17
%              Number of atoms          :  544 (1877 expanded)
%              Number of equality atoms :   96 ( 342 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f143,f144,f159,f161,f195,f325,f381,f411,f543,f548,f551,f978,f1224])).

fof(f1224,plain,
    ( ~ spl3_3
    | ~ spl3_13
    | ~ spl3_17
    | spl3_27 ),
    inference(avatar_contradiction_clause,[],[f1223])).

fof(f1223,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_17
    | spl3_27 ),
    inference(subsumption_resolution,[],[f1053,f986])).

fof(f986,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f985,f556])).

fof(f556,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_17 ),
    inference(resolution,[],[f208,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f208,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f985,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f984,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f984,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f106,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f106,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1053,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_13
    | ~ spl3_17
    | spl3_27 ),
    inference(forward_demodulation,[],[f1052,f95])).

fof(f1052,plain,
    ( ! [X0] : ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl3_13
    | ~ spl3_17
    | spl3_27 ),
    inference(subsumption_resolution,[],[f1043,f87])).

fof(f87,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1043,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl3_13
    | ~ spl3_17
    | spl3_27 ),
    inference(resolution,[],[f983,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f983,plain,
    ( ~ v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_17
    | spl3_27 ),
    inference(forward_demodulation,[],[f982,f556])).

fof(f982,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),k1_xboole_0)
    | ~ spl3_13
    | spl3_27 ),
    inference(forward_demodulation,[],[f309,f177])).

fof(f309,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),sK1)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl3_27
  <=> v1_partfun1(k2_funct_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f978,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f977])).

fof(f977,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f976,f863])).

fof(f863,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f565,f556])).

fof(f565,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f561,f95])).

fof(f561,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f107,f177])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f976,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f975,f95])).

fof(f975,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f974,f570])).

fof(f570,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f142,f556])).

fof(f142,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_9
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f974,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f967,f568])).

fof(f568,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f98,f556])).

fof(f98,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f967,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(superposition,[],[f82,f952])).

fof(f952,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f563,f556])).

fof(f563,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f490,f177])).

fof(f490,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f132,f479])).

fof(f479,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f477,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f47])).

fof(f47,plain,
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

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f477,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f56,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f56,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f132,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_7
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f551,plain,
    ( ~ spl3_18
    | spl3_17 ),
    inference(avatar_split_clause,[],[f406,f206,f211])).

fof(f211,plain,
    ( spl3_18
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f406,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f548,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f546,f107])).

fof(f546,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f545,f490])).

fof(f545,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f544,f142])).

fof(f544,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f537,f98])).

fof(f537,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(superposition,[],[f82,f521])).

fof(f521,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f137,f519])).

fof(f519,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f515,f54])).

fof(f515,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_14 ),
    inference(superposition,[],[f181,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f181,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f137,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_8
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f543,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f541,f103])).

fof(f103,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f541,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f540,f490])).

fof(f540,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f539,f142])).

fof(f539,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f536,f98])).

fof(f536,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(superposition,[],[f81,f521])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f411,plain,
    ( spl3_13
    | spl3_14 ),
    inference(avatar_split_clause,[],[f410,f179,f175])).

fof(f410,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f401,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f401,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f381,plain,
    ( ~ spl3_3
    | ~ spl3_27
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f380,f101,f97,f307,f105])).

fof(f380,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),sK1)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f378,f98])).

fof(f378,plain,
    ( ~ v1_partfun1(k2_funct_1(sK2),sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(resolution,[],[f103,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f325,plain,
    ( ~ spl3_13
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl3_13
    | spl3_18 ),
    inference(subsumption_resolution,[],[f321,f87])).

fof(f321,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_13
    | spl3_18 ),
    inference(backward_demodulation,[],[f213,f177])).

fof(f213,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f195,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f187,f120])).

fof(f120,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f187,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f161,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f160,f135,f118])).

fof(f160,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f156,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f156,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f159,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f158,f130,f118])).

fof(f158,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f155,f52])).

fof(f155,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f144,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f113,f97,f118])).

fof(f113,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f143,plain,
    ( ~ spl3_4
    | spl3_9 ),
    inference(avatar_split_clause,[],[f112,f140,f118])).

fof(f112,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f57,f105,f101,f97])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (19766)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.47  % (19758)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (19747)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (19766)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f1225,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f108,f143,f144,f159,f161,f195,f325,f381,f411,f543,f548,f551,f978,f1224])).
% 0.20/0.47  fof(f1224,plain,(
% 0.20/0.47    ~spl3_3 | ~spl3_13 | ~spl3_17 | spl3_27),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f1223])).
% 0.20/0.47  fof(f1223,plain,(
% 0.20/0.47    $false | (~spl3_3 | ~spl3_13 | ~spl3_17 | spl3_27)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1053,f986])).
% 0.20/0.47  fof(f986,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_13 | ~spl3_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f985,f556])).
% 0.20/0.47  fof(f556,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~spl3_17),
% 0.20/0.47    inference(resolution,[],[f208,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    v1_xboole_0(sK2) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f206])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    spl3_17 <=> v1_xboole_0(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f985,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f984,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f984,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_13)),
% 0.20/0.48    inference(forward_demodulation,[],[f106,f177])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl3_13 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f1053,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_13 | ~spl3_17 | spl3_27)),
% 0.20/0.48    inference(forward_demodulation,[],[f1052,f95])).
% 0.20/0.48  fof(f1052,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl3_13 | ~spl3_17 | spl3_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f1043,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f1043,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_xboole_0(k1_xboole_0)) ) | (~spl3_13 | ~spl3_17 | spl3_27)),
% 0.20/0.48    inference(resolution,[],[f983,f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.20/0.48  fof(f983,plain,(
% 0.20/0.48    ~v1_partfun1(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl3_13 | ~spl3_17 | spl3_27)),
% 0.20/0.48    inference(forward_demodulation,[],[f982,f556])).
% 0.20/0.48  fof(f982,plain,(
% 0.20/0.48    ~v1_partfun1(k2_funct_1(sK2),k1_xboole_0) | (~spl3_13 | spl3_27)),
% 0.20/0.48    inference(forward_demodulation,[],[f309,f177])).
% 0.20/0.48  fof(f309,plain,(
% 0.20/0.48    ~v1_partfun1(k2_funct_1(sK2),sK1) | spl3_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f307])).
% 0.20/0.48  fof(f307,plain,(
% 0.20/0.48    spl3_27 <=> v1_partfun1(k2_funct_1(sK2),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.48  fof(f978,plain,(
% 0.20/0.48    ~spl3_1 | spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f977])).
% 0.20/0.48  fof(f977,plain,(
% 0.20/0.48    $false | (~spl3_1 | spl3_3 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f976,f863])).
% 0.20/0.48  fof(f863,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f565,f556])).
% 0.20/0.48  fof(f565,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_13)),
% 0.20/0.48    inference(forward_demodulation,[],[f561,f95])).
% 0.20/0.48  fof(f561,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_13)),
% 0.20/0.48    inference(backward_demodulation,[],[f107,f177])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f105])).
% 0.20/0.48  fof(f976,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_1 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f975,f95])).
% 0.20/0.48  fof(f975,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl3_1 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f974,f570])).
% 0.20/0.48  fof(f570,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_9 | ~spl3_17)),
% 0.20/0.48    inference(backward_demodulation,[],[f142,f556])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK2)) | ~spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl3_9 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f974,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_1 | ~spl3_7 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f967,f568])).
% 0.20/0.48  fof(f568,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_1 | ~spl3_17)),
% 0.20/0.48    inference(backward_demodulation,[],[f98,f556])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f967,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_7 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(superposition,[],[f82,f952])).
% 0.20/0.48  fof(f952,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_7 | ~spl3_13 | ~spl3_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f563,f556])).
% 0.20/0.48  fof(f563,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_7 | ~spl3_13)),
% 0.20/0.48    inference(backward_demodulation,[],[f490,f177])).
% 0.20/0.48  fof(f490,plain,(
% 0.20/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_7),
% 0.20/0.48    inference(forward_demodulation,[],[f132,f479])).
% 0.20/0.48  fof(f479,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f477,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f21])).
% 0.20/0.48  fof(f21,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.48  fof(f477,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(superposition,[],[f56,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f48])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl3_7 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.48  fof(f551,plain,(
% 0.20/0.48    ~spl3_18 | spl3_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f406,f206,f211])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    spl3_18 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.48  fof(f406,plain,(
% 0.20/0.48    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f54,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.48  fof(f548,plain,(
% 0.20/0.48    ~spl3_1 | spl3_3 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f547])).
% 0.20/0.48  fof(f547,plain,(
% 0.20/0.48    $false | (~spl3_1 | spl3_3 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f546,f107])).
% 0.20/0.48  fof(f546,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_1 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.48    inference(forward_demodulation,[],[f545,f490])).
% 0.20/0.48  fof(f545,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_1 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f544,f142])).
% 0.20/0.48  fof(f544,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_8 | ~spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f537,f98])).
% 0.20/0.48  fof(f537,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_14)),
% 0.20/0.48    inference(superposition,[],[f82,f521])).
% 0.20/0.48  fof(f521,plain,(
% 0.20/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_14)),
% 0.20/0.48    inference(backward_demodulation,[],[f137,f519])).
% 0.20/0.48  fof(f519,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK2) | ~spl3_14),
% 0.20/0.48    inference(subsumption_resolution,[],[f515,f54])).
% 0.20/0.48  fof(f515,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_14),
% 0.20/0.48    inference(superposition,[],[f181,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f179])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    spl3_14 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f135])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl3_8 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f543,plain,(
% 0.20/0.48    ~spl3_1 | spl3_2 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f542])).
% 0.20/0.48  fof(f542,plain,(
% 0.20/0.48    $false | (~spl3_1 | spl3_2 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f541,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f541,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_1 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.48    inference(forward_demodulation,[],[f540,f490])).
% 0.20/0.48  fof(f540,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl3_1 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f539,f142])).
% 0.20/0.48  fof(f539,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_8 | ~spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f536,f98])).
% 0.20/0.48  fof(f536,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_14)),
% 0.20/0.48    inference(superposition,[],[f81,f521])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f411,plain,(
% 0.20/0.48    spl3_13 | spl3_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f410,f179,f175])).
% 0.20/0.48  fof(f410,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f401,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f48])).
% 0.20/0.48  fof(f401,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(resolution,[],[f54,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f381,plain,(
% 0.20/0.48    ~spl3_3 | ~spl3_27 | ~spl3_1 | spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f380,f101,f97,f307,f105])).
% 0.20/0.48  fof(f380,plain,(
% 0.20/0.48    ~v1_partfun1(k2_funct_1(sK2),sK1) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_1 | spl3_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f378,f98])).
% 0.20/0.48  fof(f378,plain,(
% 0.20/0.48    ~v1_partfun1(k2_funct_1(sK2),sK1) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.20/0.48    inference(resolution,[],[f103,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    ~spl3_13 | spl3_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f324])).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    $false | (~spl3_13 | spl3_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f321,f87])).
% 0.20/0.48  fof(f321,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl3_13 | spl3_18)),
% 0.20/0.48    inference(backward_demodulation,[],[f213,f177])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ~v1_xboole_0(sK1) | spl3_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f211])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    $false | spl3_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f187,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl3_4 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f54,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~spl3_4 | spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f160,f135,f118])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f156,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f48])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f55,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    v2_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f48])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ~spl3_4 | spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f158,f130,f118])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f155,f52])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f55,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ~spl3_4 | spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f113,f97,f118])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f52,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ~spl3_4 | spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f112,f140,f118])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f52,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f57,f105,f101,f97])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f48])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (19766)------------------------------
% 0.20/0.48  % (19766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19766)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (19766)Memory used [KB]: 6524
% 0.20/0.48  % (19766)Time elapsed: 0.071 s
% 0.20/0.48  % (19766)------------------------------
% 0.20/0.48  % (19766)------------------------------
% 0.20/0.48  % (19746)Success in time 0.127 s
%------------------------------------------------------------------------------
