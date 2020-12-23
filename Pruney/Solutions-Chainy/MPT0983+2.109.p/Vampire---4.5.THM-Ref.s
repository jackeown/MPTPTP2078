%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 517 expanded)
%              Number of leaves         :   45 ( 176 expanded)
%              Depth                    :   18
%              Number of atoms          :  610 (2356 expanded)
%              Number of equality atoms :   61 ( 124 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f183,f185,f272,f275,f277,f286,f288,f387,f401,f405,f407,f447,f618,f671,f676,f690,f1000,f1068,f1076,f1079])).

fof(f1079,plain,(
    spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1077])).

fof(f1077,plain,
    ( $false
    | spl6_66 ),
    inference(resolution,[],[f1075,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1075,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_66 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1073,plain,
    ( spl6_66
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f1076,plain,
    ( ~ spl6_34
    | ~ spl6_66
    | ~ spl6_54
    | spl6_65 ),
    inference(avatar_split_clause,[],[f1071,f1065,f687,f1073,f495])).

fof(f495,plain,
    ( spl6_34
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f687,plain,
    ( spl6_54
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f1065,plain,
    ( spl6_65
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f1071,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_54
    | spl6_65 ),
    inference(forward_demodulation,[],[f1070,f689])).

fof(f689,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f687])).

fof(f1070,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl6_65 ),
    inference(resolution,[],[f1067,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1067,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_65 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1068,plain,
    ( ~ spl6_34
    | ~ spl6_65
    | spl6_2
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f1059,f687,f115,f1065,f495])).

fof(f115,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1059,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_54 ),
    inference(superposition,[],[f104,f689])).

fof(f104,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1000,plain,
    ( ~ spl6_45
    | ~ spl6_34
    | spl6_53
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f999,f180,f683,f495,f589])).

fof(f589,plain,
    ( spl6_45
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f683,plain,
    ( spl6_53
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f180,plain,
    ( spl6_5
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f999,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f991,f102])).

fof(f102,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f991,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f75,f986])).

fof(f986,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f984,f182])).

fof(f182,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f180])).

fof(f984,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f791,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
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
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
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
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
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
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f791,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(X10,X11,sK1,sK0,sK2,sK3) ) ),
    inference(resolution,[],[f605,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f605,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(X2,sK3) = k1_partfun1(X0,X1,sK1,sK0,X2,sK3) ) ),
    inference(resolution,[],[f63,f242])).

fof(f242,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f97,f61])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f690,plain,
    ( ~ spl6_53
    | spl6_54
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f681,f673,f687,f683])).

fof(f673,plain,
    ( spl6_52
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f681,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl6_52 ),
    inference(resolution,[],[f675,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f675,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f673])).

fof(f676,plain,
    ( ~ spl6_34
    | spl6_52 ),
    inference(avatar_split_clause,[],[f606,f673,f495])).

fof(f606,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f92,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f671,plain,(
    spl6_34 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | spl6_34 ),
    inference(resolution,[],[f658,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f658,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl6_34 ),
    inference(resolution,[],[f603,f63])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_34 ),
    inference(resolution,[],[f497,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f497,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f495])).

fof(f618,plain,(
    spl6_45 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl6_45 ),
    inference(resolution,[],[f615,f79])).

fof(f615,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_45 ),
    inference(resolution,[],[f597,f60])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_45 ),
    inference(resolution,[],[f591,f76])).

fof(f591,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f589])).

fof(f447,plain,
    ( spl6_1
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl6_1
    | ~ spl6_26 ),
    inference(resolution,[],[f440,f206])).

fof(f206,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f100,f166])).

fof(f166,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f162,f155])).

fof(f155,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f71,f146])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f143,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f143,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X3)
      | k1_xboole_0 = k2_zfmisc_1(X3,X4) ) ),
    inference(resolution,[],[f136,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f135,f66])).

fof(f135,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | X4 = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f131,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f131,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK5(X1,X2),X1)
      | ~ v1_xboole_0(X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f129,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f129,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | X4 = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f122,f77])).

fof(f122,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK5(X2,X1),X2)
      | ~ r1_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f87,f89])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f141,f66])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f136,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f100,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f440,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl6_1
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f113,f438])).

fof(f438,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_26 ),
    inference(resolution,[],[f421,f162])).

fof(f421,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f409,f146])).

fof(f409,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f60,f382])).

fof(f382,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl6_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f113,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f407,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl6_25 ),
    inference(resolution,[],[f378,f62])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f378,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl6_25
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f405,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl6_24 ),
    inference(resolution,[],[f374,f59])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f374,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl6_24
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f401,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl6_27 ),
    inference(resolution,[],[f386,f100])).

fof(f386,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl6_27
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f387,plain,
    ( ~ spl6_13
    | ~ spl6_24
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_25
    | ~ spl6_16
    | spl6_1
    | spl6_26
    | ~ spl6_27
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f370,f180,f384,f380,f111,f269,f376,f265,f261,f372,f257])).

fof(f257,plain,
    ( spl6_13
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f261,plain,
    ( spl6_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f265,plain,
    ( spl6_15
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f269,plain,
    ( spl6_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f370,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f93,f182])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f288,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f271,f63])).

fof(f271,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f269])).

fof(f286,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl6_14 ),
    inference(resolution,[],[f263,f60])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f277,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl6_15 ),
    inference(resolution,[],[f267,f61])).

fof(f267,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f265])).

fof(f275,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f259,f58])).

fof(f259,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f272,plain,
    ( ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_3 ),
    inference(avatar_split_clause,[],[f254,f172,f269,f265,f261,f257])).

fof(f172,plain,
    ( spl6_3
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f254,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(resolution,[],[f99,f174])).

fof(f174,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f172])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f185,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f178,f71])).

fof(f178,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_4
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f183,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f168,f180,f176,f172])).

fof(f168,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f95,f64])).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f118,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f65,f115,f111])).

fof(f65,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (22700)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.49  % (22693)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (22708)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.52  % (22704)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (22712)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (22713)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (22692)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (22714)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (22695)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (22694)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (22720)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (22697)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.54  % (22706)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.54  % (22701)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  % (22696)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.54  % (22710)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.54  % (22715)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.54  % (22698)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  % (22721)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.55  % (22717)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.55  % (22711)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.55  % (22699)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.55  % (22719)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.55  % (22705)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.55  % (22702)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.55  % (22714)Refutation not found, incomplete strategy% (22714)------------------------------
% 0.19/0.55  % (22714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (22714)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (22714)Memory used [KB]: 10874
% 0.19/0.55  % (22714)Time elapsed: 0.114 s
% 0.19/0.55  % (22714)------------------------------
% 0.19/0.55  % (22714)------------------------------
% 0.19/0.55  % (22716)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.55  % (22707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.55  % (22709)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.56  % (22718)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.56  % (22703)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.61  % (22704)Refutation found. Thanks to Tanya!
% 0.19/0.61  % SZS status Theorem for theBenchmark
% 0.19/0.61  % SZS output start Proof for theBenchmark
% 0.19/0.61  fof(f1080,plain,(
% 0.19/0.61    $false),
% 0.19/0.61    inference(avatar_sat_refutation,[],[f118,f183,f185,f272,f275,f277,f286,f288,f387,f401,f405,f407,f447,f618,f671,f676,f690,f1000,f1068,f1076,f1079])).
% 0.19/0.61  fof(f1079,plain,(
% 0.19/0.61    spl6_66),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f1077])).
% 0.19/0.61  fof(f1077,plain,(
% 0.19/0.61    $false | spl6_66),
% 0.19/0.61    inference(resolution,[],[f1075,f105])).
% 0.19/0.61  fof(f105,plain,(
% 0.19/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.61    inference(equality_resolution,[],[f86])).
% 0.19/0.61  fof(f86,plain,(
% 0.19/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.61    inference(cnf_transformation,[],[f52])).
% 0.19/0.61  fof(f52,plain,(
% 0.19/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.61    inference(flattening,[],[f51])).
% 0.19/0.61  fof(f51,plain,(
% 0.19/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.61    inference(nnf_transformation,[],[f4])).
% 0.19/0.61  fof(f4,axiom,(
% 0.19/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.61  fof(f1075,plain,(
% 0.19/0.61    ~r1_tarski(sK0,sK0) | spl6_66),
% 0.19/0.61    inference(avatar_component_clause,[],[f1073])).
% 0.19/0.61  fof(f1073,plain,(
% 0.19/0.61    spl6_66 <=> r1_tarski(sK0,sK0)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.19/0.61  fof(f1076,plain,(
% 0.19/0.61    ~spl6_34 | ~spl6_66 | ~spl6_54 | spl6_65),
% 0.19/0.61    inference(avatar_split_clause,[],[f1071,f1065,f687,f1073,f495])).
% 0.19/0.61  fof(f495,plain,(
% 0.19/0.61    spl6_34 <=> v1_relat_1(sK3)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.19/0.61  fof(f687,plain,(
% 0.19/0.61    spl6_54 <=> sK0 = k2_relat_1(sK3)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.19/0.61  fof(f1065,plain,(
% 0.19/0.61    spl6_65 <=> v5_relat_1(sK3,sK0)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.19/0.61  fof(f1071,plain,(
% 0.19/0.61    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK3) | (~spl6_54 | spl6_65)),
% 0.19/0.61    inference(forward_demodulation,[],[f1070,f689])).
% 0.19/0.61  fof(f689,plain,(
% 0.19/0.61    sK0 = k2_relat_1(sK3) | ~spl6_54),
% 0.19/0.61    inference(avatar_component_clause,[],[f687])).
% 0.19/0.61  fof(f1070,plain,(
% 0.19/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl6_65),
% 0.19/0.61    inference(resolution,[],[f1067,f82])).
% 0.19/0.61  fof(f82,plain,(
% 0.19/0.61    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f49])).
% 0.19/0.61  fof(f49,plain,(
% 0.19/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.61    inference(nnf_transformation,[],[f29])).
% 0.19/0.61  fof(f29,plain,(
% 0.19/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.61    inference(ennf_transformation,[],[f8])).
% 0.19/0.61  fof(f8,axiom,(
% 0.19/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.61  fof(f1067,plain,(
% 0.19/0.61    ~v5_relat_1(sK3,sK0) | spl6_65),
% 0.19/0.61    inference(avatar_component_clause,[],[f1065])).
% 0.19/0.61  fof(f1068,plain,(
% 0.19/0.61    ~spl6_34 | ~spl6_65 | spl6_2 | ~spl6_54),
% 0.19/0.61    inference(avatar_split_clause,[],[f1059,f687,f115,f1065,f495])).
% 0.19/0.61  fof(f115,plain,(
% 0.19/0.61    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.61  fof(f1059,plain,(
% 0.19/0.61    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_54),
% 0.19/0.61    inference(superposition,[],[f104,f689])).
% 0.19/0.61  fof(f104,plain,(
% 0.19/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.61    inference(equality_resolution,[],[f84])).
% 0.19/0.61  fof(f84,plain,(
% 0.19/0.61    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f50])).
% 0.19/0.61  fof(f50,plain,(
% 0.19/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.61    inference(nnf_transformation,[],[f31])).
% 0.19/0.61  fof(f31,plain,(
% 0.19/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.61    inference(flattening,[],[f30])).
% 0.19/0.61  fof(f30,plain,(
% 0.19/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.61    inference(ennf_transformation,[],[f15])).
% 0.19/0.61  fof(f15,axiom,(
% 0.19/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.19/0.61  fof(f1000,plain,(
% 0.19/0.61    ~spl6_45 | ~spl6_34 | spl6_53 | ~spl6_5),
% 0.19/0.61    inference(avatar_split_clause,[],[f999,f180,f683,f495,f589])).
% 0.19/0.61  fof(f589,plain,(
% 0.19/0.61    spl6_45 <=> v1_relat_1(sK2)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.19/0.61  fof(f683,plain,(
% 0.19/0.61    spl6_53 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.19/0.61  fof(f180,plain,(
% 0.19/0.61    spl6_5 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.61  fof(f999,plain,(
% 0.19/0.61    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_5),
% 0.19/0.61    inference(forward_demodulation,[],[f991,f102])).
% 0.19/0.61  fof(f102,plain,(
% 0.19/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.19/0.61    inference(definition_unfolding,[],[f73,f67])).
% 0.19/0.61  fof(f67,plain,(
% 0.19/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f19])).
% 0.19/0.61  fof(f19,axiom,(
% 0.19/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.61  fof(f73,plain,(
% 0.19/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.61    inference(cnf_transformation,[],[f11])).
% 0.19/0.61  fof(f11,axiom,(
% 0.19/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.61  fof(f991,plain,(
% 0.19/0.61    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_5),
% 0.19/0.61    inference(superposition,[],[f75,f986])).
% 0.19/0.61  fof(f986,plain,(
% 0.19/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_5),
% 0.19/0.61    inference(forward_demodulation,[],[f984,f182])).
% 0.19/0.61  fof(f182,plain,(
% 0.19/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_5),
% 0.19/0.61    inference(avatar_component_clause,[],[f180])).
% 0.19/0.61  fof(f984,plain,(
% 0.19/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.19/0.61    inference(resolution,[],[f791,f60])).
% 0.19/0.61  fof(f60,plain,(
% 0.19/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f44,plain,(
% 0.19/0.61    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.19/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f43,f42])).
% 0.19/0.61  fof(f42,plain,(
% 0.19/0.61    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.61    introduced(choice_axiom,[])).
% 0.19/0.61  fof(f43,plain,(
% 0.19/0.61    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.19/0.61    introduced(choice_axiom,[])).
% 0.19/0.61  fof(f24,plain,(
% 0.19/0.61    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.61    inference(flattening,[],[f23])).
% 0.19/0.61  fof(f23,plain,(
% 0.19/0.61    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.61    inference(ennf_transformation,[],[f22])).
% 0.19/0.61  fof(f22,negated_conjecture,(
% 0.19/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.19/0.61    inference(negated_conjecture,[],[f21])).
% 0.19/0.61  fof(f21,conjecture,(
% 0.19/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.19/0.61  fof(f791,plain,(
% 0.19/0.61    ( ! [X10,X11] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k5_relat_1(sK2,sK3) = k1_partfun1(X10,X11,sK1,sK0,sK2,sK3)) )),
% 0.19/0.61    inference(resolution,[],[f605,f58])).
% 0.19/0.61  fof(f58,plain,(
% 0.19/0.61    v1_funct_1(sK2)),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f605,plain,(
% 0.19/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,sK3) = k1_partfun1(X0,X1,sK1,sK0,X2,sK3)) )),
% 0.19/0.61    inference(resolution,[],[f63,f242])).
% 0.19/0.61  fof(f242,plain,(
% 0.19/0.61    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X9)) )),
% 0.19/0.61    inference(resolution,[],[f97,f61])).
% 0.19/0.61  fof(f61,plain,(
% 0.19/0.61    v1_funct_1(sK3)),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f97,plain,(
% 0.19/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f39])).
% 0.19/0.61  fof(f39,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.61    inference(flattening,[],[f38])).
% 0.19/0.61  fof(f38,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.61    inference(ennf_transformation,[],[f18])).
% 0.19/0.61  fof(f18,axiom,(
% 0.19/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.19/0.61  fof(f63,plain,(
% 0.19/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f75,plain,(
% 0.19/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f26])).
% 0.19/0.61  fof(f26,plain,(
% 0.19/0.61    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.61    inference(ennf_transformation,[],[f10])).
% 0.19/0.61  fof(f10,axiom,(
% 0.19/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.19/0.61  fof(f690,plain,(
% 0.19/0.61    ~spl6_53 | spl6_54 | ~spl6_52),
% 0.19/0.61    inference(avatar_split_clause,[],[f681,f673,f687,f683])).
% 0.19/0.61  fof(f673,plain,(
% 0.19/0.61    spl6_52 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.19/0.61  fof(f681,plain,(
% 0.19/0.61    sK0 = k2_relat_1(sK3) | ~r1_tarski(sK0,k2_relat_1(sK3)) | ~spl6_52),
% 0.19/0.61    inference(resolution,[],[f675,f87])).
% 0.19/0.61  fof(f87,plain,(
% 0.19/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f52])).
% 0.19/0.61  fof(f675,plain,(
% 0.19/0.61    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_52),
% 0.19/0.61    inference(avatar_component_clause,[],[f673])).
% 0.19/0.61  fof(f676,plain,(
% 0.19/0.61    ~spl6_34 | spl6_52),
% 0.19/0.61    inference(avatar_split_clause,[],[f606,f673,f495])).
% 0.19/0.61  fof(f606,plain,(
% 0.19/0.61    r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.19/0.61    inference(resolution,[],[f63,f123])).
% 0.19/0.61  fof(f123,plain,(
% 0.19/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 0.19/0.61    inference(resolution,[],[f92,f81])).
% 0.19/0.61  fof(f81,plain,(
% 0.19/0.61    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f49])).
% 0.19/0.61  fof(f92,plain,(
% 0.19/0.61    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.61    inference(cnf_transformation,[],[f33])).
% 0.19/0.61  fof(f33,plain,(
% 0.19/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.61    inference(ennf_transformation,[],[f13])).
% 0.19/0.61  fof(f13,axiom,(
% 0.19/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.61  fof(f671,plain,(
% 0.19/0.61    spl6_34),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f669])).
% 0.19/0.61  fof(f669,plain,(
% 0.19/0.61    $false | spl6_34),
% 0.19/0.61    inference(resolution,[],[f658,f79])).
% 0.19/0.61  fof(f79,plain,(
% 0.19/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.61    inference(cnf_transformation,[],[f9])).
% 0.19/0.61  fof(f9,axiom,(
% 0.19/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.61  fof(f658,plain,(
% 0.19/0.61    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl6_34),
% 0.19/0.61    inference(resolution,[],[f603,f63])).
% 0.19/0.61  fof(f603,plain,(
% 0.19/0.61    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_34),
% 0.19/0.61    inference(resolution,[],[f497,f76])).
% 0.19/0.61  fof(f76,plain,(
% 0.19/0.61    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f27])).
% 0.19/0.61  fof(f27,plain,(
% 0.19/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.61    inference(ennf_transformation,[],[f7])).
% 0.19/0.61  fof(f7,axiom,(
% 0.19/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.61  fof(f497,plain,(
% 0.19/0.61    ~v1_relat_1(sK3) | spl6_34),
% 0.19/0.61    inference(avatar_component_clause,[],[f495])).
% 0.19/0.61  fof(f618,plain,(
% 0.19/0.61    spl6_45),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f616])).
% 0.19/0.61  fof(f616,plain,(
% 0.19/0.61    $false | spl6_45),
% 0.19/0.61    inference(resolution,[],[f615,f79])).
% 0.19/0.61  fof(f615,plain,(
% 0.19/0.61    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_45),
% 0.19/0.61    inference(resolution,[],[f597,f60])).
% 0.19/0.61  fof(f597,plain,(
% 0.19/0.61    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_45),
% 0.19/0.61    inference(resolution,[],[f591,f76])).
% 0.19/0.61  fof(f591,plain,(
% 0.19/0.61    ~v1_relat_1(sK2) | spl6_45),
% 0.19/0.61    inference(avatar_component_clause,[],[f589])).
% 0.19/0.61  fof(f447,plain,(
% 0.19/0.61    spl6_1 | ~spl6_26),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f446])).
% 0.19/0.61  fof(f446,plain,(
% 0.19/0.61    $false | (spl6_1 | ~spl6_26)),
% 0.19/0.61    inference(resolution,[],[f440,f206])).
% 0.19/0.61  fof(f206,plain,(
% 0.19/0.61    v2_funct_1(k1_xboole_0)),
% 0.19/0.61    inference(superposition,[],[f100,f166])).
% 0.19/0.61  fof(f166,plain,(
% 0.19/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.19/0.61    inference(resolution,[],[f162,f155])).
% 0.19/0.61  fof(f155,plain,(
% 0.19/0.61    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.61    inference(superposition,[],[f71,f146])).
% 0.19/0.61  fof(f146,plain,(
% 0.19/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.19/0.61    inference(resolution,[],[f143,f66])).
% 0.19/0.61  fof(f66,plain,(
% 0.19/0.61    v1_xboole_0(k1_xboole_0)),
% 0.19/0.61    inference(cnf_transformation,[],[f3])).
% 0.19/0.61  fof(f3,axiom,(
% 0.19/0.61    v1_xboole_0(k1_xboole_0)),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.61  fof(f143,plain,(
% 0.19/0.61    ( ! [X4,X3] : (~v1_xboole_0(X3) | k1_xboole_0 = k2_zfmisc_1(X3,X4)) )),
% 0.19/0.61    inference(resolution,[],[f136,f80])).
% 0.19/0.61  fof(f80,plain,(
% 0.19/0.61    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f28])).
% 0.19/0.61  fof(f28,plain,(
% 0.19/0.61    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.19/0.61    inference(ennf_transformation,[],[f5])).
% 0.19/0.61  fof(f5,axiom,(
% 0.19/0.61    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.19/0.61  fof(f136,plain,(
% 0.19/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.61    inference(resolution,[],[f135,f66])).
% 0.19/0.61  fof(f135,plain,(
% 0.19/0.61    ( ! [X4,X5] : (~v1_xboole_0(X4) | X4 = X5 | ~v1_xboole_0(X5)) )),
% 0.19/0.61    inference(resolution,[],[f131,f77])).
% 0.19/0.61  fof(f77,plain,(
% 0.19/0.61    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f48])).
% 0.19/0.61  fof(f48,plain,(
% 0.19/0.61    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 0.19/0.61  fof(f47,plain,(
% 0.19/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.19/0.61    introduced(choice_axiom,[])).
% 0.19/0.61  fof(f46,plain,(
% 0.19/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.61    inference(rectify,[],[f45])).
% 0.19/0.61  fof(f45,plain,(
% 0.19/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.61    inference(nnf_transformation,[],[f1])).
% 0.19/0.61  fof(f1,axiom,(
% 0.19/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.61  fof(f131,plain,(
% 0.19/0.61    ( ! [X2,X1] : (r2_hidden(sK5(X1,X2),X1) | ~v1_xboole_0(X2) | X1 = X2) )),
% 0.19/0.61    inference(resolution,[],[f129,f89])).
% 0.19/0.61  fof(f89,plain,(
% 0.19/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f56])).
% 0.19/0.61  fof(f56,plain,(
% 0.19/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).
% 0.19/0.61  fof(f55,plain,(
% 0.19/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.19/0.61    introduced(choice_axiom,[])).
% 0.19/0.61  fof(f54,plain,(
% 0.19/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.61    inference(rectify,[],[f53])).
% 0.19/0.61  fof(f53,plain,(
% 0.19/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.61    inference(nnf_transformation,[],[f32])).
% 0.19/0.61  fof(f32,plain,(
% 0.19/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.61    inference(ennf_transformation,[],[f2])).
% 0.19/0.61  fof(f2,axiom,(
% 0.19/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.61  fof(f129,plain,(
% 0.19/0.61    ( ! [X4,X5] : (~r1_tarski(X4,X5) | X4 = X5 | ~v1_xboole_0(X5)) )),
% 0.19/0.61    inference(resolution,[],[f122,f77])).
% 0.19/0.61  fof(f122,plain,(
% 0.19/0.61    ( ! [X2,X1] : (r2_hidden(sK5(X2,X1),X2) | ~r1_tarski(X1,X2) | X1 = X2) )),
% 0.19/0.61    inference(resolution,[],[f87,f89])).
% 0.19/0.61  fof(f71,plain,(
% 0.19/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.61    inference(cnf_transformation,[],[f17])).
% 0.19/0.61  fof(f17,axiom,(
% 0.19/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.19/0.61  fof(f162,plain,(
% 0.19/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.19/0.61    inference(resolution,[],[f141,f66])).
% 0.19/0.61  fof(f141,plain,(
% 0.19/0.61    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) )),
% 0.19/0.61    inference(resolution,[],[f136,f74])).
% 0.19/0.61  fof(f74,plain,(
% 0.19/0.61    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f25])).
% 0.19/0.61  fof(f25,plain,(
% 0.19/0.61    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.61    inference(ennf_transformation,[],[f6])).
% 0.19/0.61  fof(f6,axiom,(
% 0.19/0.61    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.61  fof(f100,plain,(
% 0.19/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.19/0.61    inference(definition_unfolding,[],[f69,f67])).
% 0.19/0.61  fof(f69,plain,(
% 0.19/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.61    inference(cnf_transformation,[],[f12])).
% 0.19/0.61  fof(f12,axiom,(
% 0.19/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.19/0.61  fof(f440,plain,(
% 0.19/0.61    ~v2_funct_1(k1_xboole_0) | (spl6_1 | ~spl6_26)),
% 0.19/0.61    inference(backward_demodulation,[],[f113,f438])).
% 0.19/0.61  fof(f438,plain,(
% 0.19/0.61    k1_xboole_0 = sK2 | ~spl6_26),
% 0.19/0.61    inference(resolution,[],[f421,f162])).
% 0.19/0.61  fof(f421,plain,(
% 0.19/0.61    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_26),
% 0.19/0.61    inference(forward_demodulation,[],[f409,f146])).
% 0.19/0.61  fof(f409,plain,(
% 0.19/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_26),
% 0.19/0.61    inference(backward_demodulation,[],[f60,f382])).
% 0.19/0.61  fof(f382,plain,(
% 0.19/0.61    k1_xboole_0 = sK0 | ~spl6_26),
% 0.19/0.61    inference(avatar_component_clause,[],[f380])).
% 0.19/0.61  fof(f380,plain,(
% 0.19/0.61    spl6_26 <=> k1_xboole_0 = sK0),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.19/0.61  fof(f113,plain,(
% 0.19/0.61    ~v2_funct_1(sK2) | spl6_1),
% 0.19/0.61    inference(avatar_component_clause,[],[f111])).
% 0.19/0.61  fof(f111,plain,(
% 0.19/0.61    spl6_1 <=> v2_funct_1(sK2)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.61  fof(f407,plain,(
% 0.19/0.61    spl6_25),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f406])).
% 0.19/0.61  fof(f406,plain,(
% 0.19/0.61    $false | spl6_25),
% 0.19/0.61    inference(resolution,[],[f378,f62])).
% 0.19/0.61  fof(f62,plain,(
% 0.19/0.61    v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f378,plain,(
% 0.19/0.61    ~v1_funct_2(sK3,sK1,sK0) | spl6_25),
% 0.19/0.61    inference(avatar_component_clause,[],[f376])).
% 0.19/0.61  fof(f376,plain,(
% 0.19/0.61    spl6_25 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.19/0.61  fof(f405,plain,(
% 0.19/0.61    spl6_24),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f404])).
% 0.19/0.61  fof(f404,plain,(
% 0.19/0.61    $false | spl6_24),
% 0.19/0.61    inference(resolution,[],[f374,f59])).
% 0.19/0.61  fof(f59,plain,(
% 0.19/0.61    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f374,plain,(
% 0.19/0.61    ~v1_funct_2(sK2,sK0,sK1) | spl6_24),
% 0.19/0.61    inference(avatar_component_clause,[],[f372])).
% 0.19/0.61  fof(f372,plain,(
% 0.19/0.61    spl6_24 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.19/0.61  fof(f401,plain,(
% 0.19/0.61    spl6_27),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f400])).
% 0.19/0.61  fof(f400,plain,(
% 0.19/0.61    $false | spl6_27),
% 0.19/0.61    inference(resolution,[],[f386,f100])).
% 0.19/0.61  fof(f386,plain,(
% 0.19/0.61    ~v2_funct_1(k6_partfun1(sK0)) | spl6_27),
% 0.19/0.61    inference(avatar_component_clause,[],[f384])).
% 0.19/0.61  fof(f384,plain,(
% 0.19/0.61    spl6_27 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.19/0.61  fof(f387,plain,(
% 0.19/0.61    ~spl6_13 | ~spl6_24 | ~spl6_14 | ~spl6_15 | ~spl6_25 | ~spl6_16 | spl6_1 | spl6_26 | ~spl6_27 | ~spl6_5),
% 0.19/0.61    inference(avatar_split_clause,[],[f370,f180,f384,f380,f111,f269,f376,f265,f261,f372,f257])).
% 0.19/0.61  fof(f257,plain,(
% 0.19/0.61    spl6_13 <=> v1_funct_1(sK2)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.19/0.61  fof(f261,plain,(
% 0.19/0.61    spl6_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.19/0.61  fof(f265,plain,(
% 0.19/0.61    spl6_15 <=> v1_funct_1(sK3)),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.61  fof(f269,plain,(
% 0.19/0.61    spl6_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.19/0.61  fof(f370,plain,(
% 0.19/0.61    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_5),
% 0.19/0.61    inference(superposition,[],[f93,f182])).
% 0.19/0.61  fof(f93,plain,(
% 0.19/0.61    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f35])).
% 0.19/0.61  fof(f35,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.61    inference(flattening,[],[f34])).
% 0.19/0.61  fof(f34,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.61    inference(ennf_transformation,[],[f20])).
% 0.19/0.61  fof(f20,axiom,(
% 0.19/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 0.19/0.61  fof(f288,plain,(
% 0.19/0.61    spl6_16),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f287])).
% 0.19/0.61  fof(f287,plain,(
% 0.19/0.61    $false | spl6_16),
% 0.19/0.61    inference(resolution,[],[f271,f63])).
% 0.19/0.61  fof(f271,plain,(
% 0.19/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_16),
% 0.19/0.61    inference(avatar_component_clause,[],[f269])).
% 0.19/0.61  fof(f286,plain,(
% 0.19/0.61    spl6_14),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f285])).
% 0.19/0.61  fof(f285,plain,(
% 0.19/0.61    $false | spl6_14),
% 0.19/0.61    inference(resolution,[],[f263,f60])).
% 0.19/0.61  fof(f263,plain,(
% 0.19/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_14),
% 0.19/0.61    inference(avatar_component_clause,[],[f261])).
% 0.19/0.61  fof(f277,plain,(
% 0.19/0.61    spl6_15),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f276])).
% 0.19/0.61  fof(f276,plain,(
% 0.19/0.61    $false | spl6_15),
% 0.19/0.61    inference(resolution,[],[f267,f61])).
% 0.19/0.61  fof(f267,plain,(
% 0.19/0.61    ~v1_funct_1(sK3) | spl6_15),
% 0.19/0.61    inference(avatar_component_clause,[],[f265])).
% 0.19/0.61  fof(f275,plain,(
% 0.19/0.61    spl6_13),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f274])).
% 0.19/0.61  fof(f274,plain,(
% 0.19/0.61    $false | spl6_13),
% 0.19/0.61    inference(resolution,[],[f259,f58])).
% 0.19/0.61  fof(f259,plain,(
% 0.19/0.61    ~v1_funct_1(sK2) | spl6_13),
% 0.19/0.61    inference(avatar_component_clause,[],[f257])).
% 0.19/0.61  fof(f272,plain,(
% 0.19/0.61    ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_3),
% 0.19/0.61    inference(avatar_split_clause,[],[f254,f172,f269,f265,f261,f257])).
% 0.19/0.61  fof(f172,plain,(
% 0.19/0.61    spl6_3 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.61  fof(f254,plain,(
% 0.19/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_3),
% 0.19/0.61    inference(resolution,[],[f99,f174])).
% 0.19/0.61  fof(f174,plain,(
% 0.19/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_3),
% 0.19/0.61    inference(avatar_component_clause,[],[f172])).
% 0.19/0.61  fof(f99,plain,(
% 0.19/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.19/0.61    inference(cnf_transformation,[],[f41])).
% 0.19/0.61  fof(f41,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.61    inference(flattening,[],[f40])).
% 0.19/0.61  fof(f40,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.61    inference(ennf_transformation,[],[f16])).
% 0.19/0.61  fof(f16,axiom,(
% 0.19/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.19/0.61  fof(f185,plain,(
% 0.19/0.61    spl6_4),
% 0.19/0.61    inference(avatar_contradiction_clause,[],[f184])).
% 0.19/0.61  fof(f184,plain,(
% 0.19/0.61    $false | spl6_4),
% 0.19/0.61    inference(resolution,[],[f178,f71])).
% 0.19/0.61  fof(f178,plain,(
% 0.19/0.61    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_4),
% 0.19/0.61    inference(avatar_component_clause,[],[f176])).
% 0.19/0.61  fof(f176,plain,(
% 0.19/0.61    spl6_4 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.61  fof(f183,plain,(
% 0.19/0.61    ~spl6_3 | ~spl6_4 | spl6_5),
% 0.19/0.61    inference(avatar_split_clause,[],[f168,f180,f176,f172])).
% 0.19/0.61  fof(f168,plain,(
% 0.19/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.61    inference(resolution,[],[f95,f64])).
% 0.19/0.61  fof(f64,plain,(
% 0.19/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  fof(f95,plain,(
% 0.19/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.61    inference(cnf_transformation,[],[f57])).
% 0.19/0.61  fof(f57,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.61    inference(nnf_transformation,[],[f37])).
% 0.19/0.61  fof(f37,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.61    inference(flattening,[],[f36])).
% 0.19/0.61  fof(f36,plain,(
% 0.19/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.61    inference(ennf_transformation,[],[f14])).
% 0.19/0.61  fof(f14,axiom,(
% 0.19/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.61  fof(f118,plain,(
% 0.19/0.61    ~spl6_1 | ~spl6_2),
% 0.19/0.61    inference(avatar_split_clause,[],[f65,f115,f111])).
% 0.19/0.61  fof(f65,plain,(
% 0.19/0.61    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 0.19/0.61    inference(cnf_transformation,[],[f44])).
% 0.19/0.61  % SZS output end Proof for theBenchmark
% 0.19/0.61  % (22704)------------------------------
% 0.19/0.61  % (22704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.61  % (22704)Termination reason: Refutation
% 0.19/0.61  
% 0.19/0.61  % (22704)Memory used [KB]: 6780
% 0.19/0.61  % (22704)Time elapsed: 0.181 s
% 0.19/0.61  % (22704)------------------------------
% 0.19/0.61  % (22704)------------------------------
% 1.79/0.62  % (22683)Success in time 0.259 s
%------------------------------------------------------------------------------
