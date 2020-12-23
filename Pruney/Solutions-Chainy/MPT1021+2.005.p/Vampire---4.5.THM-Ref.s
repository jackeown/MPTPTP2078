%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:50 EST 2020

% Result     : Theorem 3.59s
% Output     : Refutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  331 ( 749 expanded)
%              Number of leaves         :   80 ( 336 expanded)
%              Depth                    :   11
%              Number of atoms          : 1167 (2380 expanded)
%              Number of equality atoms :  205 ( 367 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5640,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f178,f183,f188,f193,f391,f437,f818,f838,f841,f920,f921,f925,f929,f933,f940,f944,f968,f1375,f1411,f1520,f1535,f1544,f1948,f2130,f2350,f2411,f2525,f3665,f4269,f4394,f4398,f4426,f4427,f4491,f4533,f4534,f4538,f4539,f4700,f4715,f4879,f4987,f5345,f5365,f5370,f5464,f5635,f5639])).

fof(f5639,plain,
    ( k1_xboole_0 != k2_funct_1(sK1)
    | k1_xboole_0 != k6_partfun1(sK1)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5635,plain,
    ( ~ spl6_401
    | ~ spl6_3
    | ~ spl6_6
    | spl6_402 ),
    inference(avatar_split_clause,[],[f5634,f5367,f190,f175,f5362])).

fof(f5362,plain,
    ( spl6_401
  <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_401])])).

fof(f175,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f190,plain,
    ( spl6_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f5367,plain,
    ( spl6_402
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_402])])).

fof(f5634,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_6
    | spl6_402 ),
    inference(forward_demodulation,[],[f5623,f162])).

fof(f162,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f5623,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_6
    | spl6_402 ),
    inference(unit_resulting_resolution,[],[f160,f3737,f5369,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f89])).

fof(f89,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(f5369,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0))
    | spl6_402 ),
    inference(avatar_component_clause,[],[f5367])).

fof(f3737,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f103,f2854,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f2854,plain,
    ( ! [X0] : v1_xboole_0(k5_relat_1(sK1,sK5(X0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f101,f2812,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f2812,plain,
    ( ! [X0,X1] : m1_subset_1(k5_relat_1(sK1,sK5(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f245,f237])).

fof(f237,plain,
    ( ! [X0,X1] : k1_partfun1(sK0,sK0,X0,X1,sK1,sK5(X0,X1)) = k5_relat_1(sK1,sK5(X0,X1))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f192,f140,f136,f177,f157])).

fof(f157,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f177,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f175])).

fof(f136,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK5(X0,X1),X0,X1)
      & v1_funct_1(sK5(X0,X1))
      & v5_relat_1(sK5(X0,X1),X1)
      & v4_relat_1(sK5(X0,X1),X0)
      & v1_relat_1(sK5(X0,X1))
      & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f94])).

fof(f94,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK5(X0,X1),X0,X1)
        & v1_funct_1(sK5(X0,X1))
        & v5_relat_1(sK5(X0,X1),X1)
        & v4_relat_1(sK5(X0,X1),X0)
        & v1_relat_1(sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f140,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f95])).

fof(f192,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f190])).

fof(f245,plain,
    ( ! [X0,X1] : m1_subset_1(k1_partfun1(sK0,sK0,X0,X1,sK1,sK5(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f192,f140,f136,f177,f159])).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f160,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f105,f104])).

fof(f104,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f5464,plain,
    ( spl6_40
    | ~ spl6_27
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f4942,f679,f402,f499])).

fof(f499,plain,
    ( spl6_40
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f402,plain,
    ( spl6_27
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f679,plain,
    ( spl6_52
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f4942,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl6_27
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f681,f404])).

fof(f404,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f402])).

fof(f681,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f679])).

fof(f5370,plain,
    ( ~ spl6_402
    | ~ spl6_27
    | spl6_165 ),
    inference(avatar_split_clause,[],[f4972,f2297,f402,f5367])).

fof(f2297,plain,
    ( spl6_165
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).

fof(f4972,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0))
    | ~ spl6_27
    | spl6_165 ),
    inference(backward_demodulation,[],[f2299,f404])).

fof(f2299,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl6_165 ),
    inference(avatar_component_clause,[],[f2297])).

fof(f5365,plain,
    ( spl6_401
    | ~ spl6_27
    | ~ spl6_166 ),
    inference(avatar_split_clause,[],[f5063,f2323,f402,f5362])).

fof(f2323,plain,
    ( spl6_166
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f5063,plain,
    ( m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_27
    | ~ spl6_166 ),
    inference(forward_demodulation,[],[f4973,f162])).

fof(f4973,plain,
    ( m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_27
    | ~ spl6_166 ),
    inference(backward_demodulation,[],[f2324,f404])).

fof(f2324,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_166 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f5345,plain,
    ( spl6_359
    | ~ spl6_27
    | ~ spl6_277 ),
    inference(avatar_split_clause,[],[f4981,f3662,f402,f4484])).

fof(f4484,plain,
    ( spl6_359
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_359])])).

fof(f3662,plain,
    ( spl6_277
  <=> sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_277])])).

fof(f4981,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl6_27
    | ~ spl6_277 ),
    inference(backward_demodulation,[],[f3664,f404])).

fof(f3664,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl6_277 ),
    inference(avatar_component_clause,[],[f3662])).

fof(f4987,plain,
    ( spl6_50
    | ~ spl6_3
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f4986,f402,f175,f624])).

fof(f624,plain,
    ( spl6_50
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f4986,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f4920,f162])).

fof(f4920,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f177,f404])).

fof(f4879,plain,
    ( spl6_47
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f4871,f380,f599])).

fof(f599,plain,
    ( spl6_47
  <=> v1_xboole_0(k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f380,plain,
    ( spl6_25
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f4871,plain,
    ( v1_xboole_0(k6_partfun1(sK1))
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f160,f382,f120])).

fof(f382,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f380])).

fof(f4715,plain,
    ( ~ spl6_165
    | spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f4714,f312,f170,f2297])).

fof(f170,plain,
    ( spl6_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f312,plain,
    ( spl6_12
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f4714,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f172,f314])).

fof(f314,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f312])).

fof(f172,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f170])).

fof(f4700,plain,
    ( spl6_85
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f1458,f599,f1478])).

fof(f1478,plain,
    ( spl6_85
  <=> k1_xboole_0 = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f1458,plain,
    ( k1_xboole_0 = k6_partfun1(sK1)
    | ~ spl6_47 ),
    inference(unit_resulting_resolution,[],[f101,f601,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f601,plain,
    ( v1_xboole_0(k6_partfun1(sK1))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f599])).

fof(f4539,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1)
    | k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4538,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | k6_partfun1(sK0) != k5_relat_1(sK1,k2_funct_1(sK1))
    | k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4534,plain,
    ( sK0 != k1_relat_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k2_relset_1(sK0,sK0,sK1) != k9_relat_1(sK1,sK0)
    | k2_relat_1(sK1) != k9_relat_1(sK1,k1_relat_1(sK1))
    | sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4533,plain,
    ( ~ spl6_341
    | spl6_364
    | ~ spl6_41
    | ~ spl6_270
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f4528,f4335,f3618,f510,f4530,f4351])).

fof(f4351,plain,
    ( spl6_341
  <=> v5_relat_1(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_341])])).

fof(f4530,plain,
    ( spl6_364
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_364])])).

fof(f510,plain,
    ( spl6_41
  <=> k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f3618,plain,
    ( spl6_270
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_270])])).

fof(f4335,plain,
    ( spl6_338
  <=> v2_funct_2(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_338])])).

fof(f4528,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl6_41
    | ~ spl6_270
    | ~ spl6_338 ),
    inference(forward_demodulation,[],[f4527,f512])).

fof(f512,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f510])).

fof(f4527,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl6_270
    | ~ spl6_338 ),
    inference(subsumption_resolution,[],[f4526,f3619])).

fof(f3619,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl6_270 ),
    inference(avatar_component_clause,[],[f3618])).

fof(f4526,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl6_338 ),
    inference(resolution,[],[f4337,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f4337,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ spl6_338 ),
    inference(avatar_component_clause,[],[f4335])).

fof(f4491,plain,
    ( ~ spl6_359
    | spl6_360
    | ~ spl6_270 ),
    inference(avatar_split_clause,[],[f4451,f3618,f4488,f4484])).

fof(f4488,plain,
    ( spl6_360
  <=> k1_xboole_0 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_360])])).

fof(f4451,plain,
    ( k1_xboole_0 = k2_funct_1(sK1)
    | k1_xboole_0 != k1_relat_1(k2_funct_1(sK1))
    | ~ spl6_270 ),
    inference(resolution,[],[f3619,f107])).

fof(f107,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f4427,plain,
    ( spl6_332
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f4186,f1541,f1517,f190,f175,f4307])).

fof(f4307,plain,
    ( spl6_332
  <=> k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_332])])).

fof(f1517,plain,
    ( spl6_88
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f1541,plain,
    ( spl6_90
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f4186,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f1519,f1543,f418])).

fof(f418,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k1_partfun1(X4,X5,sK0,sK0,X6,sK1) = k5_relat_1(X6,sK1)
        | ~ v1_funct_1(X6) )
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f268,f192])).

fof(f268,plain,
    ( ! [X6,X4,X5] :
        ( k1_partfun1(X4,X5,sK0,sK0,X6,sK1) = k5_relat_1(X6,sK1)
        | ~ v1_funct_1(sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6) )
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f157])).

fof(f1543,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f1519,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f4426,plain,
    ( spl6_333
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f4185,f1541,f1517,f190,f175,f4312])).

fof(f4312,plain,
    ( spl6_333
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_333])])).

fof(f4185,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f1519,f1543,f417])).

fof(f417,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_partfun1(sK0,sK0,X1,X2,sK1,X3) = k5_relat_1(sK1,X3)
        | ~ v1_funct_1(X3) )
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f267,f192])).

fof(f267,plain,
    ( ! [X2,X3,X1] :
        ( k1_partfun1(sK0,sK0,X1,X2,sK1,X3) = k5_relat_1(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f157])).

fof(f4398,plain,
    ( spl6_338
    | ~ spl6_87
    | ~ spl6_88
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f4152,f1541,f1517,f1512,f4335])).

fof(f1512,plain,
    ( spl6_87
  <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f4152,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ spl6_87
    | ~ spl6_88
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f1519,f1514,f1543,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f1514,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f1512])).

fof(f4394,plain,
    ( spl6_341
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f4148,f1541,f4351])).

fof(f4148,plain,
    ( v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f1543,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f4269,plain,
    ( spl6_270
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f4193,f1541,f3618])).

fof(f4193,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f118,f1543,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f118,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f3665,plain,
    ( spl6_277
    | ~ spl6_42
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f3660,f679,f515,f3662])).

fof(f515,plain,
    ( spl6_42
  <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f3660,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl6_42
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f517,f681])).

fof(f517,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f515])).

fof(f2525,plain,
    ( ~ spl6_92
    | spl6_1
    | ~ spl6_12
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f2524,f1550,f312,f166,f1554])).

fof(f1554,plain,
    ( spl6_92
  <=> k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f166,plain,
    ( spl6_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1550,plain,
    ( spl6_91
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f2524,plain,
    ( k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_91 ),
    inference(subsumption_resolution,[],[f2523,f1551])).

fof(f1551,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f2523,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)))
    | spl6_1
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f2522,f314])).

fof(f2522,plain,
    ( k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_1
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f950,f314])).

fof(f950,plain,
    ( k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f947,f160])).

fof(f947,plain,
    ( k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_1 ),
    inference(resolution,[],[f168,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f168,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f166])).

fof(f2411,plain,
    ( ~ spl6_167
    | spl6_165
    | ~ spl6_166 ),
    inference(avatar_split_clause,[],[f2372,f2323,f2297,f2327])).

fof(f2327,plain,
    ( spl6_167
  <=> k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f2372,plain,
    ( k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)))
    | spl6_165
    | ~ spl6_166 ),
    inference(unit_resulting_resolution,[],[f160,f2299,f2324,f124])).

fof(f2350,plain,
    ( ~ spl6_90
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | spl6_166 ),
    inference(avatar_split_clause,[],[f2349,f2323,f1517,f190,f175,f1541])).

fof(f2349,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2348,f1519])).

fof(f2348,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl6_3
    | ~ spl6_6
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2347,f192])).

fof(f2347,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl6_3
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2338,f177])).

fof(f2338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl6_166 ),
    inference(resolution,[],[f2325,f159])).

fof(f2325,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_166 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f2130,plain,
    ( ~ spl6_90
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | spl6_91 ),
    inference(avatar_split_clause,[],[f2129,f1550,f1517,f190,f175,f1541])).

fof(f2129,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_88
    | spl6_91 ),
    inference(subsumption_resolution,[],[f2128,f192])).

fof(f2128,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_88
    | spl6_91 ),
    inference(subsumption_resolution,[],[f2127,f177])).

fof(f2127,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl6_88
    | spl6_91 ),
    inference(subsumption_resolution,[],[f2118,f1519])).

fof(f2118,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_91 ),
    inference(resolution,[],[f1552,f159])).

fof(f1552,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_91 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f1948,plain,
    ( spl6_129
    | ~ spl6_3
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f1943,f355,f175,f1945])).

fof(f1945,plain,
    ( spl6_129
  <=> k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f355,plain,
    ( spl6_20
  <=> k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1943,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f357,f235])).

fof(f235,plain,
    ( ! [X0] : k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f177,f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f357,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f355])).

fof(f1544,plain,
    ( spl6_90
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f1539,f312,f190,f185,f180,f175,f1541])).

fof(f180,plain,
    ( spl6_4
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f185,plain,
    ( spl6_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1539,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1538,f192])).

fof(f1538,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1537,f187])).

fof(f187,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f185])).

fof(f1537,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1536,f182])).

fof(f182,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1536,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1505,f177])).

fof(f1505,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_12 ),
    inference(superposition,[],[f131,f314])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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

fof(f1535,plain,
    ( spl6_87
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f1534,f312,f190,f185,f180,f175,f1512])).

fof(f1534,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1533,f192])).

fof(f1533,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1532,f187])).

fof(f1532,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1531,f182])).

fof(f1531,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1504,f177])).

fof(f1504,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_12 ),
    inference(superposition,[],[f130,f314])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1520,plain,
    ( spl6_88
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f1500,f312,f307,f1517])).

fof(f307,plain,
    ( spl6_11
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1500,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f309,f314])).

fof(f309,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f307])).

fof(f1411,plain,
    ( ~ spl6_40
    | ~ spl6_7
    | spl6_39 ),
    inference(avatar_split_clause,[],[f1400,f494,f287,f499])).

fof(f287,plain,
    ( spl6_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f494,plain,
    ( spl6_39
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f1400,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ spl6_7
    | spl6_39 ),
    inference(unit_resulting_resolution,[],[f289,f495,f108])).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f495,plain,
    ( k1_xboole_0 != sK1
    | spl6_39 ),
    inference(avatar_component_clause,[],[f494])).

fof(f289,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f287])).

fof(f1375,plain,
    ( ~ spl6_50
    | spl6_25 ),
    inference(avatar_split_clause,[],[f1374,f380,f624])).

fof(f1374,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_25 ),
    inference(forward_demodulation,[],[f1365,f162])).

fof(f1365,plain,
    ( ! [X0] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f101,f381,f120])).

fof(f381,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f380])).

fof(f968,plain,
    ( spl6_52
    | ~ spl6_7
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f966,f360,f340,f287,f679])).

fof(f340,plain,
    ( spl6_17
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f360,plain,
    ( spl6_21
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f966,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl6_7
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f289,f342,f362,f125])).

fof(f362,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f360])).

fof(f342,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f340])).

fof(f944,plain,
    ( spl6_11
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f943,f190,f185,f180,f175,f307])).

fof(f943,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f942,f192])).

fof(f942,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f941,f187])).

fof(f941,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f894,f182])).

fof(f894,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f940,plain,
    ( spl6_12
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f939,f190,f185,f180,f175,f312])).

fof(f939,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f938,f192])).

fof(f938,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f937,f187])).

fof(f937,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f893,f182])).

fof(f893,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f933,plain,
    ( ~ spl6_26
    | spl6_27
    | spl6_29
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f932,f345,f190,f185,f175,f413,f402,f398])).

fof(f398,plain,
    ( spl6_26
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f413,plain,
    ( spl6_29
  <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f345,plain,
    ( spl6_18
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f932,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f931,f192])).

fof(f931,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f930,f187])).

fof(f930,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f880,f347])).

fof(f347,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f345])).

fof(f880,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f929,plain,
    ( ~ spl6_26
    | spl6_27
    | spl6_28
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f928,f345,f190,f185,f175,f406,f402,f398])).

fof(f406,plain,
    ( spl6_28
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f928,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f927,f192])).

fof(f927,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f926,f187])).

fof(f926,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f879,f347])).

fof(f879,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f925,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f924,f190,f180,f175,f340])).

fof(f924,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f923,f192])).

fof(f923,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f878,f182])).

fof(f878,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f150])).

fof(f921,plain,
    ( spl6_20
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f875,f175,f355])).

fof(f875,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f920,plain,
    ( spl6_21
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f874,f175,f360])).

fof(f874,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f145])).

fof(f841,plain,
    ( spl6_41
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f840,f345,f287,f190,f510])).

fof(f840,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f839,f289])).

fof(f839,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f833,f192])).

fof(f833,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f347,f114])).

fof(f114,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f838,plain,
    ( spl6_42
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f837,f345,f287,f190,f515])).

fof(f837,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f836,f289])).

fof(f836,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f832,f192])).

fof(f832,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f347,f113])).

fof(f113,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f818,plain,
    ( spl6_37
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f803,f287,f484])).

fof(f484,plain,
    ( spl6_37
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f803,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl6_7 ),
    inference(resolution,[],[f289,f106])).

fof(f106,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f437,plain,
    ( spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f436,f175,f287])).

fof(f436,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f285,f118])).

fof(f285,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f109])).

fof(f391,plain,
    ( spl6_18
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f390,f190,f180,f175,f345])).

fof(f390,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f389,f192])).

fof(f389,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f262,f182])).

fof(f262,plain,
    ( v2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f177,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f193,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f96,f190])).

fof(f96,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f80])).

fof(f80,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f188,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f97,f185])).

fof(f97,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f183,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f98,f180])).

fof(f98,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f178,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f99,f175])).

fof(f99,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

fof(f173,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f100,f170,f166])).

fof(f100,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (12981)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (12984)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (12983)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12989)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (12982)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12999)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (12978)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (12996)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (12992)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (12987)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12986)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (12993)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (13002)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13009)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (12991)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (13001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (13006)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (12980)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12985)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (13003)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (12979)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (12990)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.55  % (12995)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (13000)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (12997)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.55  % (12988)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.55  % (13008)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.55  % (13004)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.55  % (13005)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.56  % (12994)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 3.59/0.83  % (12983)Time limit reached!
% 3.59/0.83  % (12983)------------------------------
% 3.59/0.83  % (12983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.83  % (12983)Termination reason: Time limit
% 3.59/0.83  
% 3.59/0.83  % (12983)Memory used [KB]: 9594
% 3.59/0.83  % (12983)Time elapsed: 0.419 s
% 3.59/0.83  % (12983)------------------------------
% 3.59/0.83  % (12983)------------------------------
% 3.59/0.84  % (13004)Refutation found. Thanks to Tanya!
% 3.59/0.84  % SZS status Theorem for theBenchmark
% 3.59/0.84  % SZS output start Proof for theBenchmark
% 3.59/0.84  fof(f5640,plain,(
% 3.59/0.84    $false),
% 3.59/0.84    inference(avatar_sat_refutation,[],[f173,f178,f183,f188,f193,f391,f437,f818,f838,f841,f920,f921,f925,f929,f933,f940,f944,f968,f1375,f1411,f1520,f1535,f1544,f1948,f2130,f2350,f2411,f2525,f3665,f4269,f4394,f4398,f4426,f4427,f4491,f4533,f4534,f4538,f4539,f4700,f4715,f4879,f4987,f5345,f5365,f5370,f5464,f5635,f5639])).
% 3.59/0.84  fof(f5639,plain,(
% 3.59/0.84    k1_xboole_0 != k2_funct_1(sK1) | k1_xboole_0 != k6_partfun1(sK1) | k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 3.59/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.59/0.84  fof(f5635,plain,(
% 3.59/0.84    ~spl6_401 | ~spl6_3 | ~spl6_6 | spl6_402),
% 3.59/0.84    inference(avatar_split_clause,[],[f5634,f5367,f190,f175,f5362])).
% 3.59/0.84  fof(f5362,plain,(
% 3.59/0.84    spl6_401 <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k1_xboole_0))),
% 3.59/0.84    introduced(avatar_definition,[new_symbols(naming,[spl6_401])])).
% 3.59/0.84  fof(f175,plain,(
% 3.59/0.84    spl6_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.59/0.84    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.59/0.84  fof(f190,plain,(
% 3.59/0.84    spl6_6 <=> v1_funct_1(sK1)),
% 3.59/0.84    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 3.59/0.84  fof(f5367,plain,(
% 3.59/0.84    spl6_402 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0))),
% 3.59/0.84    introduced(avatar_definition,[new_symbols(naming,[spl6_402])])).
% 3.59/0.84  fof(f5634,plain,(
% 3.59/0.84    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_6 | spl6_402)),
% 3.59/0.84    inference(forward_demodulation,[],[f5623,f162])).
% 3.59/0.84  fof(f162,plain,(
% 3.59/0.84    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.59/0.84    inference(equality_resolution,[],[f134])).
% 3.59/0.84  fof(f134,plain,(
% 3.59/0.84    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.59/0.84    inference(cnf_transformation,[],[f93])).
% 3.59/0.84  fof(f93,plain,(
% 3.59/0.84    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.59/0.84    inference(flattening,[],[f92])).
% 3.59/0.84  fof(f92,plain,(
% 3.59/0.84    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.59/0.84    inference(nnf_transformation,[],[f7])).
% 3.59/0.84  fof(f7,axiom,(
% 3.59/0.84    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.59/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.59/0.84  fof(f5623,plain,(
% 3.59/0.84    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_3 | ~spl6_6 | spl6_402)),
% 3.59/0.84    inference(unit_resulting_resolution,[],[f160,f3737,f5369,f123])).
% 3.59/0.84  fof(f123,plain,(
% 3.59/0.84    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.84    inference(cnf_transformation,[],[f90])).
% 3.59/0.84  fof(f90,plain,(
% 3.59/0.84    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.59/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f89])).
% 3.59/0.84  fof(f89,plain,(
% 3.59/0.84    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 3.59/0.84    introduced(choice_axiom,[])).
% 3.59/0.84  fof(f54,plain,(
% 3.59/0.84    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.59/0.84    inference(flattening,[],[f53])).
% 3.59/0.84  fof(f53,plain,(
% 3.59/0.84    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.59/0.84    inference(ennf_transformation,[],[f25])).
% 3.59/0.84  fof(f25,axiom,(
% 3.59/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 3.59/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).
% 3.59/0.84  fof(f5369,plain,(
% 3.59/0.84    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0)) | spl6_402),
% 3.59/0.84    inference(avatar_component_clause,[],[f5367])).
% 3.59/0.84  fof(f3737,plain,(
% 3.59/0.84    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.84    inference(unit_resulting_resolution,[],[f103,f2854,f154])).
% 3.59/0.84  fof(f154,plain,(
% 3.59/0.84    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.59/0.84    inference(cnf_transformation,[],[f72])).
% 3.59/0.84  fof(f72,plain,(
% 3.59/0.84    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.59/0.84    inference(ennf_transformation,[],[f10])).
% 3.59/0.84  fof(f10,axiom,(
% 3.59/0.84    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.59/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 3.59/0.84  fof(f2854,plain,(
% 3.59/0.84    ( ! [X0] : (v1_xboole_0(k5_relat_1(sK1,sK5(X0,k1_xboole_0)))) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.84    inference(unit_resulting_resolution,[],[f101,f2812,f120])).
% 3.59/0.84  fof(f120,plain,(
% 3.59/0.84    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.59/0.84    inference(cnf_transformation,[],[f51])).
% 3.59/0.84  fof(f51,plain,(
% 3.59/0.84    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.59/0.84    inference(ennf_transformation,[],[f19])).
% 3.59/0.84  fof(f19,axiom,(
% 3.59/0.84    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.59/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 3.59/0.84  fof(f2812,plain,(
% 3.59/0.84    ( ! [X0,X1] : (m1_subset_1(k5_relat_1(sK1,sK5(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.84    inference(backward_demodulation,[],[f245,f237])).
% 3.59/0.84  fof(f237,plain,(
% 3.59/0.84    ( ! [X0,X1] : (k1_partfun1(sK0,sK0,X0,X1,sK1,sK5(X0,X1)) = k5_relat_1(sK1,sK5(X0,X1))) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.84    inference(unit_resulting_resolution,[],[f192,f140,f136,f177,f157])).
% 3.59/0.84  fof(f157,plain,(
% 3.59/0.84    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.84    inference(cnf_transformation,[],[f77])).
% 3.59/0.84  fof(f77,plain,(
% 3.59/0.84    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.84    inference(flattening,[],[f76])).
% 3.59/0.84  fof(f76,plain,(
% 3.59/0.84    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.84    inference(ennf_transformation,[],[f31])).
% 3.59/0.84  fof(f31,axiom,(
% 3.59/0.84    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.59/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 3.59/0.84  fof(f177,plain,(
% 3.59/0.84    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_3),
% 3.59/0.84    inference(avatar_component_clause,[],[f175])).
% 3.59/0.84  fof(f136,plain,(
% 3.59/0.84    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.84    inference(cnf_transformation,[],[f95])).
% 3.59/0.84  fof(f95,plain,(
% 3.59/0.84    ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v5_relat_1(sK5(X0,X1),X1) & v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f94])).
% 3.59/0.84  fof(f94,plain,(
% 3.59/0.84    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v5_relat_1(sK5(X0,X1),X1) & v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.59/0.84    introduced(choice_axiom,[])).
% 3.59/0.84  fof(f30,axiom,(
% 3.59/0.84    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 3.59/0.84  fof(f140,plain,(
% 3.59/0.84    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 3.59/0.84    inference(cnf_transformation,[],[f95])).
% 3.59/0.84  fof(f192,plain,(
% 3.59/0.84    v1_funct_1(sK1) | ~spl6_6),
% 3.59/0.84    inference(avatar_component_clause,[],[f190])).
% 3.59/0.85  fof(f245,plain,(
% 3.59/0.85    ( ! [X0,X1] : (m1_subset_1(k1_partfun1(sK0,sK0,X0,X1,sK1,sK5(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f192,f140,f136,f177,f159])).
% 3.59/0.85  fof(f159,plain,(
% 3.59/0.85    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f79])).
% 3.59/0.85  fof(f79,plain,(
% 3.59/0.85    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.85    inference(flattening,[],[f78])).
% 3.59/0.85  fof(f78,plain,(
% 3.59/0.85    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.85    inference(ennf_transformation,[],[f28])).
% 3.59/0.85  fof(f28,axiom,(
% 3.59/0.85    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 3.59/0.85  fof(f101,plain,(
% 3.59/0.85    v1_xboole_0(k1_xboole_0)),
% 3.59/0.85    inference(cnf_transformation,[],[f2])).
% 3.59/0.85  fof(f2,axiom,(
% 3.59/0.85    v1_xboole_0(k1_xboole_0)),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.59/0.85  fof(f103,plain,(
% 3.59/0.85    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f8])).
% 3.59/0.85  fof(f8,axiom,(
% 3.59/0.85    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.59/0.85  fof(f160,plain,(
% 3.59/0.85    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.85    inference(definition_unfolding,[],[f105,f104])).
% 3.59/0.85  fof(f104,plain,(
% 3.59/0.85    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f33])).
% 3.59/0.85  fof(f33,axiom,(
% 3.59/0.85    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 3.59/0.85  fof(f105,plain,(
% 3.59/0.85    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f23])).
% 3.59/0.85  fof(f23,axiom,(
% 3.59/0.85    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 3.59/0.85  fof(f5464,plain,(
% 3.59/0.85    spl6_40 | ~spl6_27 | ~spl6_52),
% 3.59/0.85    inference(avatar_split_clause,[],[f4942,f679,f402,f499])).
% 3.59/0.85  fof(f499,plain,(
% 3.59/0.85    spl6_40 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 3.59/0.85  fof(f402,plain,(
% 3.59/0.85    spl6_27 <=> k1_xboole_0 = sK0),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 3.59/0.85  fof(f679,plain,(
% 3.59/0.85    spl6_52 <=> sK0 = k2_relat_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 3.59/0.85  fof(f4942,plain,(
% 3.59/0.85    k1_xboole_0 = k2_relat_1(sK1) | (~spl6_27 | ~spl6_52)),
% 3.59/0.85    inference(backward_demodulation,[],[f681,f404])).
% 3.59/0.85  fof(f404,plain,(
% 3.59/0.85    k1_xboole_0 = sK0 | ~spl6_27),
% 3.59/0.85    inference(avatar_component_clause,[],[f402])).
% 3.59/0.85  fof(f681,plain,(
% 3.59/0.85    sK0 = k2_relat_1(sK1) | ~spl6_52),
% 3.59/0.85    inference(avatar_component_clause,[],[f679])).
% 3.59/0.85  fof(f5370,plain,(
% 3.59/0.85    ~spl6_402 | ~spl6_27 | spl6_165),
% 3.59/0.85    inference(avatar_split_clause,[],[f4972,f2297,f402,f5367])).
% 3.59/0.85  fof(f2297,plain,(
% 3.59/0.85    spl6_165 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).
% 3.59/0.85  fof(f4972,plain,(
% 3.59/0.85    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0)) | (~spl6_27 | spl6_165)),
% 3.59/0.85    inference(backward_demodulation,[],[f2299,f404])).
% 3.59/0.85  fof(f2299,plain,(
% 3.59/0.85    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl6_165),
% 3.59/0.85    inference(avatar_component_clause,[],[f2297])).
% 3.59/0.85  fof(f5365,plain,(
% 3.59/0.85    spl6_401 | ~spl6_27 | ~spl6_166),
% 3.59/0.85    inference(avatar_split_clause,[],[f5063,f2323,f402,f5362])).
% 3.59/0.85  fof(f2323,plain,(
% 3.59/0.85    spl6_166 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).
% 3.59/0.85  fof(f5063,plain,(
% 3.59/0.85    m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl6_27 | ~spl6_166)),
% 3.59/0.85    inference(forward_demodulation,[],[f4973,f162])).
% 3.59/0.85  fof(f4973,plain,(
% 3.59/0.85    m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_27 | ~spl6_166)),
% 3.59/0.85    inference(backward_demodulation,[],[f2324,f404])).
% 3.59/0.85  fof(f2324,plain,(
% 3.59/0.85    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_166),
% 3.59/0.85    inference(avatar_component_clause,[],[f2323])).
% 3.59/0.85  fof(f5345,plain,(
% 3.59/0.85    spl6_359 | ~spl6_27 | ~spl6_277),
% 3.59/0.85    inference(avatar_split_clause,[],[f4981,f3662,f402,f4484])).
% 3.59/0.85  fof(f4484,plain,(
% 3.59/0.85    spl6_359 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_359])])).
% 3.59/0.85  fof(f3662,plain,(
% 3.59/0.85    spl6_277 <=> sK0 = k1_relat_1(k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_277])])).
% 3.59/0.85  fof(f4981,plain,(
% 3.59/0.85    k1_xboole_0 = k1_relat_1(k2_funct_1(sK1)) | (~spl6_27 | ~spl6_277)),
% 3.59/0.85    inference(backward_demodulation,[],[f3664,f404])).
% 3.59/0.85  fof(f3664,plain,(
% 3.59/0.85    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~spl6_277),
% 3.59/0.85    inference(avatar_component_clause,[],[f3662])).
% 3.59/0.85  fof(f4987,plain,(
% 3.59/0.85    spl6_50 | ~spl6_3 | ~spl6_27),
% 3.59/0.85    inference(avatar_split_clause,[],[f4986,f402,f175,f624])).
% 3.59/0.85  fof(f624,plain,(
% 3.59/0.85    spl6_50 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 3.59/0.85  fof(f4986,plain,(
% 3.59/0.85    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_27)),
% 3.59/0.85    inference(forward_demodulation,[],[f4920,f162])).
% 3.59/0.85  fof(f4920,plain,(
% 3.59/0.85    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_3 | ~spl6_27)),
% 3.59/0.85    inference(backward_demodulation,[],[f177,f404])).
% 3.59/0.85  fof(f4879,plain,(
% 3.59/0.85    spl6_47 | ~spl6_25),
% 3.59/0.85    inference(avatar_split_clause,[],[f4871,f380,f599])).
% 3.59/0.85  fof(f599,plain,(
% 3.59/0.85    spl6_47 <=> v1_xboole_0(k6_partfun1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 3.59/0.85  fof(f380,plain,(
% 3.59/0.85    spl6_25 <=> v1_xboole_0(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 3.59/0.85  fof(f4871,plain,(
% 3.59/0.85    v1_xboole_0(k6_partfun1(sK1)) | ~spl6_25),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f160,f382,f120])).
% 3.59/0.85  fof(f382,plain,(
% 3.59/0.85    v1_xboole_0(sK1) | ~spl6_25),
% 3.59/0.85    inference(avatar_component_clause,[],[f380])).
% 3.59/0.85  fof(f4715,plain,(
% 3.59/0.85    ~spl6_165 | spl6_2 | ~spl6_12),
% 3.59/0.85    inference(avatar_split_clause,[],[f4714,f312,f170,f2297])).
% 3.59/0.85  fof(f170,plain,(
% 3.59/0.85    spl6_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.59/0.85  fof(f312,plain,(
% 3.59/0.85    spl6_12 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 3.59/0.85  fof(f4714,plain,(
% 3.59/0.85    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | (spl6_2 | ~spl6_12)),
% 3.59/0.85    inference(forward_demodulation,[],[f172,f314])).
% 3.59/0.85  fof(f314,plain,(
% 3.59/0.85    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl6_12),
% 3.59/0.85    inference(avatar_component_clause,[],[f312])).
% 3.59/0.85  fof(f172,plain,(
% 3.59/0.85    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl6_2),
% 3.59/0.85    inference(avatar_component_clause,[],[f170])).
% 3.59/0.85  fof(f4700,plain,(
% 3.59/0.85    spl6_85 | ~spl6_47),
% 3.59/0.85    inference(avatar_split_clause,[],[f1458,f599,f1478])).
% 3.59/0.85  fof(f1478,plain,(
% 3.59/0.85    spl6_85 <=> k1_xboole_0 = k6_partfun1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 3.59/0.85  fof(f1458,plain,(
% 3.59/0.85    k1_xboole_0 = k6_partfun1(sK1) | ~spl6_47),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f101,f601,f135])).
% 3.59/0.85  fof(f135,plain,(
% 3.59/0.85    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f61])).
% 3.59/0.85  fof(f61,plain,(
% 3.59/0.85    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.59/0.85    inference(ennf_transformation,[],[f6])).
% 3.59/0.85  fof(f6,axiom,(
% 3.59/0.85    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 3.59/0.85  fof(f601,plain,(
% 3.59/0.85    v1_xboole_0(k6_partfun1(sK1)) | ~spl6_47),
% 3.59/0.85    inference(avatar_component_clause,[],[f599])).
% 3.59/0.85  fof(f4539,plain,(
% 3.59/0.85    k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) | k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)))),
% 3.59/0.85    introduced(theory_tautology_sat_conflict,[])).
% 3.59/0.85  fof(f4538,plain,(
% 3.59/0.85    k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | k6_partfun1(sK0) != k5_relat_1(sK1,k2_funct_1(sK1)) | k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)))),
% 3.59/0.85    introduced(theory_tautology_sat_conflict,[])).
% 3.59/0.85  fof(f4534,plain,(
% 3.59/0.85    sK0 != k1_relat_1(sK1) | sK0 != k2_relat_1(sK1) | k2_relset_1(sK0,sK0,sK1) != k9_relat_1(sK1,sK0) | k2_relat_1(sK1) != k9_relat_1(sK1,k1_relat_1(sK1)) | sK0 = k2_relset_1(sK0,sK0,sK1)),
% 3.59/0.85    introduced(theory_tautology_sat_conflict,[])).
% 3.59/0.85  fof(f4533,plain,(
% 3.59/0.85    ~spl6_341 | spl6_364 | ~spl6_41 | ~spl6_270 | ~spl6_338),
% 3.59/0.85    inference(avatar_split_clause,[],[f4528,f4335,f3618,f510,f4530,f4351])).
% 3.59/0.85  fof(f4351,plain,(
% 3.59/0.85    spl6_341 <=> v5_relat_1(k2_funct_1(sK1),sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_341])])).
% 3.59/0.85  fof(f4530,plain,(
% 3.59/0.85    spl6_364 <=> sK0 = k1_relat_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_364])])).
% 3.59/0.85  fof(f510,plain,(
% 3.59/0.85    spl6_41 <=> k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 3.59/0.85  fof(f3618,plain,(
% 3.59/0.85    spl6_270 <=> v1_relat_1(k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_270])])).
% 3.59/0.85  fof(f4335,plain,(
% 3.59/0.85    spl6_338 <=> v2_funct_2(k2_funct_1(sK1),sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_338])])).
% 3.59/0.85  fof(f4528,plain,(
% 3.59/0.85    sK0 = k1_relat_1(sK1) | ~v5_relat_1(k2_funct_1(sK1),sK0) | (~spl6_41 | ~spl6_270 | ~spl6_338)),
% 3.59/0.85    inference(forward_demodulation,[],[f4527,f512])).
% 3.59/0.85  fof(f512,plain,(
% 3.59/0.85    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~spl6_41),
% 3.59/0.85    inference(avatar_component_clause,[],[f510])).
% 3.59/0.85  fof(f4527,plain,(
% 3.59/0.85    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | (~spl6_270 | ~spl6_338)),
% 3.59/0.85    inference(subsumption_resolution,[],[f4526,f3619])).
% 3.59/0.85  fof(f3619,plain,(
% 3.59/0.85    v1_relat_1(k2_funct_1(sK1)) | ~spl6_270),
% 3.59/0.85    inference(avatar_component_clause,[],[f3618])).
% 3.59/0.85  fof(f4526,plain,(
% 3.59/0.85    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl6_338),
% 3.59/0.85    inference(resolution,[],[f4337,f125])).
% 3.59/0.85  fof(f125,plain,(
% 3.59/0.85    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f91])).
% 3.59/0.85  fof(f91,plain,(
% 3.59/0.85    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.85    inference(nnf_transformation,[],[f56])).
% 3.59/0.85  fof(f56,plain,(
% 3.59/0.85    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.85    inference(flattening,[],[f55])).
% 3.59/0.85  fof(f55,plain,(
% 3.59/0.85    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.59/0.85    inference(ennf_transformation,[],[f27])).
% 3.59/0.85  fof(f27,axiom,(
% 3.59/0.85    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 3.59/0.85  fof(f4337,plain,(
% 3.59/0.85    v2_funct_2(k2_funct_1(sK1),sK0) | ~spl6_338),
% 3.59/0.85    inference(avatar_component_clause,[],[f4335])).
% 3.59/0.85  fof(f4491,plain,(
% 3.59/0.85    ~spl6_359 | spl6_360 | ~spl6_270),
% 3.59/0.85    inference(avatar_split_clause,[],[f4451,f3618,f4488,f4484])).
% 3.59/0.85  fof(f4488,plain,(
% 3.59/0.85    spl6_360 <=> k1_xboole_0 = k2_funct_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_360])])).
% 3.59/0.85  fof(f4451,plain,(
% 3.59/0.85    k1_xboole_0 = k2_funct_1(sK1) | k1_xboole_0 != k1_relat_1(k2_funct_1(sK1)) | ~spl6_270),
% 3.59/0.85    inference(resolution,[],[f3619,f107])).
% 3.59/0.85  fof(f107,plain,(
% 3.59/0.85    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f42])).
% 3.59/0.85  fof(f42,plain,(
% 3.59/0.85    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.59/0.85    inference(flattening,[],[f41])).
% 3.59/0.85  fof(f41,plain,(
% 3.59/0.85    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.59/0.85    inference(ennf_transformation,[],[f15])).
% 3.59/0.85  fof(f15,axiom,(
% 3.59/0.85    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 3.59/0.85  fof(f4427,plain,(
% 3.59/0.85    spl6_332 | ~spl6_3 | ~spl6_6 | ~spl6_88 | ~spl6_90),
% 3.59/0.85    inference(avatar_split_clause,[],[f4186,f1541,f1517,f190,f175,f4307])).
% 3.59/0.85  fof(f4307,plain,(
% 3.59/0.85    spl6_332 <=> k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_332])])).
% 3.59/0.85  fof(f1517,plain,(
% 3.59/0.85    spl6_88 <=> v1_funct_1(k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 3.59/0.85  fof(f1541,plain,(
% 3.59/0.85    spl6_90 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 3.59/0.85  fof(f4186,plain,(
% 3.59/0.85    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl6_3 | ~spl6_6 | ~spl6_88 | ~spl6_90)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f1519,f1543,f418])).
% 3.59/0.85  fof(f418,plain,(
% 3.59/0.85    ( ! [X6,X4,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_partfun1(X4,X5,sK0,sK0,X6,sK1) = k5_relat_1(X6,sK1) | ~v1_funct_1(X6)) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.85    inference(subsumption_resolution,[],[f268,f192])).
% 3.59/0.85  fof(f268,plain,(
% 3.59/0.85    ( ! [X6,X4,X5] : (k1_partfun1(X4,X5,sK0,sK0,X6,sK1) = k5_relat_1(X6,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X6)) ) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f157])).
% 3.59/0.85  fof(f1543,plain,(
% 3.59/0.85    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_90),
% 3.59/0.85    inference(avatar_component_clause,[],[f1541])).
% 3.59/0.85  fof(f1519,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_1(sK1)) | ~spl6_88),
% 3.59/0.85    inference(avatar_component_clause,[],[f1517])).
% 3.59/0.85  fof(f4426,plain,(
% 3.59/0.85    spl6_333 | ~spl6_3 | ~spl6_6 | ~spl6_88 | ~spl6_90),
% 3.59/0.85    inference(avatar_split_clause,[],[f4185,f1541,f1517,f190,f175,f4312])).
% 3.59/0.85  fof(f4312,plain,(
% 3.59/0.85    spl6_333 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_333])])).
% 3.59/0.85  fof(f4185,plain,(
% 3.59/0.85    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl6_3 | ~spl6_6 | ~spl6_88 | ~spl6_90)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f1519,f1543,f417])).
% 3.59/0.85  fof(f417,plain,(
% 3.59/0.85    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_partfun1(sK0,sK0,X1,X2,sK1,X3) = k5_relat_1(sK1,X3) | ~v1_funct_1(X3)) ) | (~spl6_3 | ~spl6_6)),
% 3.59/0.85    inference(subsumption_resolution,[],[f267,f192])).
% 3.59/0.85  fof(f267,plain,(
% 3.59/0.85    ( ! [X2,X3,X1] : (k1_partfun1(sK0,sK0,X1,X2,sK1,X3) = k5_relat_1(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_1(sK1)) ) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f157])).
% 3.59/0.85  fof(f4398,plain,(
% 3.59/0.85    spl6_338 | ~spl6_87 | ~spl6_88 | ~spl6_90),
% 3.59/0.85    inference(avatar_split_clause,[],[f4152,f1541,f1517,f1512,f4335])).
% 3.59/0.85  fof(f1512,plain,(
% 3.59/0.85    spl6_87 <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 3.59/0.85  fof(f4152,plain,(
% 3.59/0.85    v2_funct_2(k2_funct_1(sK1),sK0) | (~spl6_87 | ~spl6_88 | ~spl6_90)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f1519,f1514,f1543,f150])).
% 3.59/0.85  fof(f150,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f67])).
% 3.59/0.85  fof(f67,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.85    inference(flattening,[],[f66])).
% 3.59/0.85  fof(f66,plain,(
% 3.59/0.85    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.85    inference(ennf_transformation,[],[f26])).
% 3.59/0.85  fof(f26,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 3.59/0.85  fof(f1514,plain,(
% 3.59/0.85    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~spl6_87),
% 3.59/0.85    inference(avatar_component_clause,[],[f1512])).
% 3.59/0.85  fof(f4394,plain,(
% 3.59/0.85    spl6_341 | ~spl6_90),
% 3.59/0.85    inference(avatar_split_clause,[],[f4148,f1541,f4351])).
% 3.59/0.85  fof(f4148,plain,(
% 3.59/0.85    v5_relat_1(k2_funct_1(sK1),sK0) | ~spl6_90),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f1543,f145])).
% 3.59/0.85  fof(f145,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f64])).
% 3.59/0.85  fof(f64,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.85    inference(ennf_transformation,[],[f18])).
% 3.59/0.85  fof(f18,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.59/0.85  fof(f4269,plain,(
% 3.59/0.85    spl6_270 | ~spl6_90),
% 3.59/0.85    inference(avatar_split_clause,[],[f4193,f1541,f3618])).
% 3.59/0.85  fof(f4193,plain,(
% 3.59/0.85    v1_relat_1(k2_funct_1(sK1)) | ~spl6_90),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f118,f1543,f109])).
% 3.59/0.85  fof(f109,plain,(
% 3.59/0.85    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f43])).
% 3.59/0.85  fof(f43,plain,(
% 3.59/0.85    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.59/0.85    inference(ennf_transformation,[],[f11])).
% 3.59/0.85  fof(f11,axiom,(
% 3.59/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.59/0.85  fof(f118,plain,(
% 3.59/0.85    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f13])).
% 3.59/0.85  fof(f13,axiom,(
% 3.59/0.85    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.59/0.85  fof(f3665,plain,(
% 3.59/0.85    spl6_277 | ~spl6_42 | ~spl6_52),
% 3.59/0.85    inference(avatar_split_clause,[],[f3660,f679,f515,f3662])).
% 3.59/0.85  fof(f515,plain,(
% 3.59/0.85    spl6_42 <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 3.59/0.85  fof(f3660,plain,(
% 3.59/0.85    sK0 = k1_relat_1(k2_funct_1(sK1)) | (~spl6_42 | ~spl6_52)),
% 3.59/0.85    inference(forward_demodulation,[],[f517,f681])).
% 3.59/0.85  fof(f517,plain,(
% 3.59/0.85    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl6_42),
% 3.59/0.85    inference(avatar_component_clause,[],[f515])).
% 3.59/0.85  fof(f2525,plain,(
% 3.59/0.85    ~spl6_92 | spl6_1 | ~spl6_12 | ~spl6_91),
% 3.59/0.85    inference(avatar_split_clause,[],[f2524,f1550,f312,f166,f1554])).
% 3.59/0.85  fof(f1554,plain,(
% 3.59/0.85    spl6_92 <=> k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 3.59/0.85  fof(f166,plain,(
% 3.59/0.85    spl6_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.59/0.85  fof(f1550,plain,(
% 3.59/0.85    spl6_91 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 3.59/0.85  fof(f2524,plain,(
% 3.59/0.85    k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) | (spl6_1 | ~spl6_12 | ~spl6_91)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2523,f1551])).
% 3.59/0.85  fof(f1551,plain,(
% 3.59/0.85    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_91),
% 3.59/0.85    inference(avatar_component_clause,[],[f1550])).
% 3.59/0.85  fof(f2523,plain,(
% 3.59/0.85    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) | (spl6_1 | ~spl6_12)),
% 3.59/0.85    inference(forward_demodulation,[],[f2522,f314])).
% 3.59/0.85  fof(f2522,plain,(
% 3.59/0.85    k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl6_1 | ~spl6_12)),
% 3.59/0.85    inference(forward_demodulation,[],[f950,f314])).
% 3.59/0.85  fof(f950,plain,(
% 3.59/0.85    k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_1),
% 3.59/0.85    inference(subsumption_resolution,[],[f947,f160])).
% 3.59/0.85  fof(f947,plain,(
% 3.59/0.85    k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_1),
% 3.59/0.85    inference(resolution,[],[f168,f124])).
% 3.59/0.85  fof(f124,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f90])).
% 3.59/0.85  fof(f168,plain,(
% 3.59/0.85    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl6_1),
% 3.59/0.85    inference(avatar_component_clause,[],[f166])).
% 3.59/0.85  fof(f2411,plain,(
% 3.59/0.85    ~spl6_167 | spl6_165 | ~spl6_166),
% 3.59/0.85    inference(avatar_split_clause,[],[f2372,f2323,f2297,f2327])).
% 3.59/0.85  fof(f2327,plain,(
% 3.59/0.85    spl6_167 <=> k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) = k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).
% 3.59/0.85  fof(f2372,plain,(
% 3.59/0.85    k11_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK4(sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))) | (spl6_165 | ~spl6_166)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f160,f2299,f2324,f124])).
% 3.59/0.85  fof(f2350,plain,(
% 3.59/0.85    ~spl6_90 | ~spl6_3 | ~spl6_6 | ~spl6_88 | spl6_166),
% 3.59/0.85    inference(avatar_split_clause,[],[f2349,f2323,f1517,f190,f175,f1541])).
% 3.59/0.85  fof(f2349,plain,(
% 3.59/0.85    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl6_3 | ~spl6_6 | ~spl6_88 | spl6_166)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2348,f1519])).
% 3.59/0.85  fof(f2348,plain,(
% 3.59/0.85    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | (~spl6_3 | ~spl6_6 | spl6_166)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2347,f192])).
% 3.59/0.85  fof(f2347,plain,(
% 3.59/0.85    ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | (~spl6_3 | spl6_166)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2338,f177])).
% 3.59/0.85  fof(f2338,plain,(
% 3.59/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl6_166),
% 3.59/0.85    inference(resolution,[],[f2325,f159])).
% 3.59/0.85  fof(f2325,plain,(
% 3.59/0.85    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_166),
% 3.59/0.85    inference(avatar_component_clause,[],[f2323])).
% 3.59/0.85  fof(f2130,plain,(
% 3.59/0.85    ~spl6_90 | ~spl6_3 | ~spl6_6 | ~spl6_88 | spl6_91),
% 3.59/0.85    inference(avatar_split_clause,[],[f2129,f1550,f1517,f190,f175,f1541])).
% 3.59/0.85  fof(f2129,plain,(
% 3.59/0.85    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl6_3 | ~spl6_6 | ~spl6_88 | spl6_91)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2128,f192])).
% 3.59/0.85  fof(f2128,plain,(
% 3.59/0.85    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_88 | spl6_91)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2127,f177])).
% 3.59/0.85  fof(f2127,plain,(
% 3.59/0.85    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl6_88 | spl6_91)),
% 3.59/0.85    inference(subsumption_resolution,[],[f2118,f1519])).
% 3.59/0.85  fof(f2118,plain,(
% 3.59/0.85    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_91),
% 3.59/0.85    inference(resolution,[],[f1552,f159])).
% 3.59/0.85  fof(f1552,plain,(
% 3.59/0.85    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_91),
% 3.59/0.85    inference(avatar_component_clause,[],[f1550])).
% 3.59/0.85  fof(f1948,plain,(
% 3.59/0.85    spl6_129 | ~spl6_3 | ~spl6_20),
% 3.59/0.85    inference(avatar_split_clause,[],[f1943,f355,f175,f1945])).
% 3.59/0.85  fof(f1945,plain,(
% 3.59/0.85    spl6_129 <=> k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).
% 3.59/0.85  fof(f355,plain,(
% 3.59/0.85    spl6_20 <=> k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 3.59/0.85  fof(f1943,plain,(
% 3.59/0.85    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0) | (~spl6_3 | ~spl6_20)),
% 3.59/0.85    inference(forward_demodulation,[],[f357,f235])).
% 3.59/0.85  fof(f235,plain,(
% 3.59/0.85    ( ! [X0] : (k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)) ) | ~spl6_3),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f177,f155])).
% 3.59/0.85  fof(f155,plain,(
% 3.59/0.85    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.85    inference(cnf_transformation,[],[f73])).
% 3.59/0.85  fof(f73,plain,(
% 3.59/0.85    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.85    inference(ennf_transformation,[],[f21])).
% 3.59/0.85  fof(f21,axiom,(
% 3.59/0.85    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 3.59/0.85  fof(f357,plain,(
% 3.59/0.85    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) | ~spl6_20),
% 3.59/0.85    inference(avatar_component_clause,[],[f355])).
% 3.59/0.85  fof(f1544,plain,(
% 3.59/0.85    spl6_90 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12),
% 3.59/0.85    inference(avatar_split_clause,[],[f1539,f312,f190,f185,f180,f175,f1541])).
% 3.59/0.85  fof(f180,plain,(
% 3.59/0.85    spl6_4 <=> v3_funct_2(sK1,sK0,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.59/0.85  fof(f185,plain,(
% 3.59/0.85    spl6_5 <=> v1_funct_2(sK1,sK0,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.59/0.85  fof(f1539,plain,(
% 3.59/0.85    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1538,f192])).
% 3.59/0.85  fof(f1538,plain,(
% 3.59/0.85    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1537,f187])).
% 3.59/0.85  fof(f187,plain,(
% 3.59/0.85    v1_funct_2(sK1,sK0,sK0) | ~spl6_5),
% 3.59/0.85    inference(avatar_component_clause,[],[f185])).
% 3.59/0.85  fof(f1537,plain,(
% 3.59/0.85    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1536,f182])).
% 3.59/0.85  fof(f182,plain,(
% 3.59/0.85    v3_funct_2(sK1,sK0,sK0) | ~spl6_4),
% 3.59/0.85    inference(avatar_component_clause,[],[f180])).
% 3.59/0.85  fof(f1536,plain,(
% 3.59/0.85    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1505,f177])).
% 3.59/0.85  fof(f1505,plain,(
% 3.59/0.85    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_12),
% 3.59/0.85    inference(superposition,[],[f131,f314])).
% 3.59/0.85  fof(f131,plain,(
% 3.59/0.85    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f60])).
% 3.59/0.85  fof(f60,plain,(
% 3.59/0.85    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.59/0.85    inference(flattening,[],[f59])).
% 3.59/0.85  fof(f59,plain,(
% 3.59/0.85    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.59/0.85    inference(ennf_transformation,[],[f29])).
% 3.59/0.85  fof(f29,axiom,(
% 3.59/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 3.59/0.85  fof(f1535,plain,(
% 3.59/0.85    spl6_87 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12),
% 3.59/0.85    inference(avatar_split_clause,[],[f1534,f312,f190,f185,f180,f175,f1512])).
% 3.59/0.85  fof(f1534,plain,(
% 3.59/0.85    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1533,f192])).
% 3.59/0.85  fof(f1533,plain,(
% 3.59/0.85    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1532,f187])).
% 3.59/0.85  fof(f1532,plain,(
% 3.59/0.85    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1531,f182])).
% 3.59/0.85  fof(f1531,plain,(
% 3.59/0.85    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_12)),
% 3.59/0.85    inference(subsumption_resolution,[],[f1504,f177])).
% 3.59/0.85  fof(f1504,plain,(
% 3.59/0.85    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_12),
% 3.59/0.85    inference(superposition,[],[f130,f314])).
% 3.59/0.85  fof(f130,plain,(
% 3.59/0.85    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f60])).
% 3.59/0.85  fof(f1520,plain,(
% 3.59/0.85    spl6_88 | ~spl6_11 | ~spl6_12),
% 3.59/0.85    inference(avatar_split_clause,[],[f1500,f312,f307,f1517])).
% 3.59/0.85  fof(f307,plain,(
% 3.59/0.85    spl6_11 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 3.59/0.85  fof(f1500,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_1(sK1)) | (~spl6_11 | ~spl6_12)),
% 3.59/0.85    inference(backward_demodulation,[],[f309,f314])).
% 3.59/0.85  fof(f309,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl6_11),
% 3.59/0.85    inference(avatar_component_clause,[],[f307])).
% 3.59/0.85  fof(f1411,plain,(
% 3.59/0.85    ~spl6_40 | ~spl6_7 | spl6_39),
% 3.59/0.85    inference(avatar_split_clause,[],[f1400,f494,f287,f499])).
% 3.59/0.85  fof(f287,plain,(
% 3.59/0.85    spl6_7 <=> v1_relat_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 3.59/0.85  fof(f494,plain,(
% 3.59/0.85    spl6_39 <=> k1_xboole_0 = sK1),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 3.59/0.85  fof(f1400,plain,(
% 3.59/0.85    k1_xboole_0 != k2_relat_1(sK1) | (~spl6_7 | spl6_39)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f289,f495,f108])).
% 3.59/0.85  fof(f108,plain,(
% 3.59/0.85    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f42])).
% 3.59/0.85  fof(f495,plain,(
% 3.59/0.85    k1_xboole_0 != sK1 | spl6_39),
% 3.59/0.85    inference(avatar_component_clause,[],[f494])).
% 3.59/0.85  fof(f289,plain,(
% 3.59/0.85    v1_relat_1(sK1) | ~spl6_7),
% 3.59/0.85    inference(avatar_component_clause,[],[f287])).
% 3.59/0.85  fof(f1375,plain,(
% 3.59/0.85    ~spl6_50 | spl6_25),
% 3.59/0.85    inference(avatar_split_clause,[],[f1374,f380,f624])).
% 3.59/0.85  fof(f1374,plain,(
% 3.59/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | spl6_25),
% 3.59/0.85    inference(forward_demodulation,[],[f1365,f162])).
% 3.59/0.85  fof(f1365,plain,(
% 3.59/0.85    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | spl6_25),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f101,f381,f120])).
% 3.59/0.85  fof(f381,plain,(
% 3.59/0.85    ~v1_xboole_0(sK1) | spl6_25),
% 3.59/0.85    inference(avatar_component_clause,[],[f380])).
% 3.59/0.85  fof(f968,plain,(
% 3.59/0.85    spl6_52 | ~spl6_7 | ~spl6_17 | ~spl6_21),
% 3.59/0.85    inference(avatar_split_clause,[],[f966,f360,f340,f287,f679])).
% 3.59/0.85  fof(f340,plain,(
% 3.59/0.85    spl6_17 <=> v2_funct_2(sK1,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 3.59/0.85  fof(f360,plain,(
% 3.59/0.85    spl6_21 <=> v5_relat_1(sK1,sK0)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 3.59/0.85  fof(f966,plain,(
% 3.59/0.85    sK0 = k2_relat_1(sK1) | (~spl6_7 | ~spl6_17 | ~spl6_21)),
% 3.59/0.85    inference(unit_resulting_resolution,[],[f289,f342,f362,f125])).
% 3.59/0.85  fof(f362,plain,(
% 3.59/0.85    v5_relat_1(sK1,sK0) | ~spl6_21),
% 3.59/0.85    inference(avatar_component_clause,[],[f360])).
% 3.59/0.85  fof(f342,plain,(
% 3.59/0.85    v2_funct_2(sK1,sK0) | ~spl6_17),
% 3.59/0.85    inference(avatar_component_clause,[],[f340])).
% 3.59/0.85  fof(f944,plain,(
% 3.59/0.85    spl6_11 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6),
% 3.59/0.85    inference(avatar_split_clause,[],[f943,f190,f185,f180,f175,f307])).
% 3.59/0.85  fof(f943,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 3.59/0.85    inference(subsumption_resolution,[],[f942,f192])).
% 3.59/0.85  fof(f942,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 3.59/0.85    inference(subsumption_resolution,[],[f941,f187])).
% 3.59/0.85  fof(f941,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4)),
% 3.59/0.85    inference(subsumption_resolution,[],[f894,f182])).
% 3.59/0.85  fof(f894,plain,(
% 3.59/0.85    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f128])).
% 3.59/0.85  fof(f128,plain,(
% 3.59/0.85    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f60])).
% 3.59/0.85  fof(f940,plain,(
% 3.59/0.85    spl6_12 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6),
% 3.59/0.85    inference(avatar_split_clause,[],[f939,f190,f185,f180,f175,f312])).
% 3.59/0.85  fof(f939,plain,(
% 3.59/0.85    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 3.59/0.85    inference(subsumption_resolution,[],[f938,f192])).
% 3.59/0.85  fof(f938,plain,(
% 3.59/0.85    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 3.59/0.85    inference(subsumption_resolution,[],[f937,f187])).
% 3.59/0.85  fof(f937,plain,(
% 3.59/0.85    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4)),
% 3.59/0.85    inference(subsumption_resolution,[],[f893,f182])).
% 3.59/0.85  fof(f893,plain,(
% 3.59/0.85    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f127])).
% 3.59/0.85  fof(f127,plain,(
% 3.59/0.85    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f58])).
% 3.59/0.85  fof(f58,plain,(
% 3.59/0.85    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.59/0.85    inference(flattening,[],[f57])).
% 3.59/0.85  fof(f57,plain,(
% 3.59/0.85    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.59/0.85    inference(ennf_transformation,[],[f32])).
% 3.59/0.85  fof(f32,axiom,(
% 3.59/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 3.59/0.85  fof(f933,plain,(
% 3.59/0.85    ~spl6_26 | spl6_27 | spl6_29 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_18),
% 3.59/0.85    inference(avatar_split_clause,[],[f932,f345,f190,f185,f175,f413,f402,f398])).
% 3.59/0.85  fof(f398,plain,(
% 3.59/0.85    spl6_26 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 3.59/0.85  fof(f413,plain,(
% 3.59/0.85    spl6_29 <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 3.59/0.85  fof(f345,plain,(
% 3.59/0.85    spl6_18 <=> v2_funct_1(sK1)),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 3.59/0.85  fof(f932,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | (~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_18)),
% 3.59/0.85    inference(subsumption_resolution,[],[f931,f192])).
% 3.59/0.85  fof(f931,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_5 | ~spl6_18)),
% 3.59/0.85    inference(subsumption_resolution,[],[f930,f187])).
% 3.59/0.85  fof(f930,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_18)),
% 3.59/0.85    inference(subsumption_resolution,[],[f880,f347])).
% 3.59/0.85  fof(f347,plain,(
% 3.59/0.85    v2_funct_1(sK1) | ~spl6_18),
% 3.59/0.85    inference(avatar_component_clause,[],[f345])).
% 3.59/0.85  fof(f880,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f152])).
% 3.59/0.85  fof(f152,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f69])).
% 3.59/0.85  fof(f69,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.59/0.85    inference(flattening,[],[f68])).
% 3.59/0.85  fof(f68,plain,(
% 3.59/0.85    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.59/0.85    inference(ennf_transformation,[],[f34])).
% 3.59/0.85  fof(f34,axiom,(
% 3.59/0.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 3.59/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 3.59/0.85  fof(f929,plain,(
% 3.59/0.85    ~spl6_26 | spl6_27 | spl6_28 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_18),
% 3.59/0.85    inference(avatar_split_clause,[],[f928,f345,f190,f185,f175,f406,f402,f398])).
% 3.59/0.85  fof(f406,plain,(
% 3.59/0.85    spl6_28 <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 3.59/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 3.59/0.85  fof(f928,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | (~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_18)),
% 3.59/0.85    inference(subsumption_resolution,[],[f927,f192])).
% 3.59/0.85  fof(f927,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_5 | ~spl6_18)),
% 3.59/0.85    inference(subsumption_resolution,[],[f926,f187])).
% 3.59/0.85  fof(f926,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_18)),
% 3.59/0.85    inference(subsumption_resolution,[],[f879,f347])).
% 3.59/0.85  fof(f879,plain,(
% 3.59/0.85    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f151])).
% 3.59/0.85  fof(f151,plain,(
% 3.59/0.85    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.59/0.85    inference(cnf_transformation,[],[f69])).
% 3.59/0.85  fof(f925,plain,(
% 3.59/0.85    spl6_17 | ~spl6_3 | ~spl6_4 | ~spl6_6),
% 3.59/0.85    inference(avatar_split_clause,[],[f924,f190,f180,f175,f340])).
% 3.59/0.85  fof(f924,plain,(
% 3.59/0.85    v2_funct_2(sK1,sK0) | (~spl6_3 | ~spl6_4 | ~spl6_6)),
% 3.59/0.85    inference(subsumption_resolution,[],[f923,f192])).
% 3.59/0.85  fof(f923,plain,(
% 3.59/0.85    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4)),
% 3.59/0.85    inference(subsumption_resolution,[],[f878,f182])).
% 3.59/0.85  fof(f878,plain,(
% 3.59/0.85    v2_funct_2(sK1,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f150])).
% 3.59/0.85  fof(f921,plain,(
% 3.59/0.85    spl6_20 | ~spl6_3),
% 3.59/0.85    inference(avatar_split_clause,[],[f875,f175,f355])).
% 3.59/0.85  fof(f875,plain,(
% 3.59/0.85    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) | ~spl6_3),
% 3.59/0.85    inference(resolution,[],[f177,f146])).
% 3.82/0.85  fof(f146,plain,(
% 3.82/0.85    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/0.85    inference(cnf_transformation,[],[f65])).
% 3.82/0.85  fof(f65,plain,(
% 3.82/0.85    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/0.85    inference(ennf_transformation,[],[f24])).
% 3.82/0.85  fof(f24,axiom,(
% 3.82/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.82/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 3.82/0.85  fof(f920,plain,(
% 3.82/0.85    spl6_21 | ~spl6_3),
% 3.82/0.85    inference(avatar_split_clause,[],[f874,f175,f360])).
% 3.82/0.85  fof(f874,plain,(
% 3.82/0.85    v5_relat_1(sK1,sK0) | ~spl6_3),
% 3.82/0.85    inference(resolution,[],[f177,f145])).
% 3.82/0.85  fof(f841,plain,(
% 3.82/0.85    spl6_41 | ~spl6_6 | ~spl6_7 | ~spl6_18),
% 3.82/0.85    inference(avatar_split_clause,[],[f840,f345,f287,f190,f510])).
% 3.82/0.85  fof(f840,plain,(
% 3.82/0.85    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | (~spl6_6 | ~spl6_7 | ~spl6_18)),
% 3.82/0.85    inference(subsumption_resolution,[],[f839,f289])).
% 3.82/0.85  fof(f839,plain,(
% 3.82/0.85    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_6 | ~spl6_18)),
% 3.82/0.85    inference(subsumption_resolution,[],[f833,f192])).
% 3.82/0.85  fof(f833,plain,(
% 3.82/0.85    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_18),
% 3.82/0.85    inference(resolution,[],[f347,f114])).
% 3.82/0.85  fof(f114,plain,(
% 3.82/0.85    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.85    inference(cnf_transformation,[],[f47])).
% 3.82/0.85  fof(f47,plain,(
% 3.82/0.85    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/0.85    inference(flattening,[],[f46])).
% 3.82/0.85  fof(f46,plain,(
% 3.82/0.85    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.82/0.85    inference(ennf_transformation,[],[f16])).
% 3.82/0.85  fof(f16,axiom,(
% 3.82/0.85    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.82/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 3.82/0.85  fof(f838,plain,(
% 3.82/0.85    spl6_42 | ~spl6_6 | ~spl6_7 | ~spl6_18),
% 3.82/0.85    inference(avatar_split_clause,[],[f837,f345,f287,f190,f515])).
% 3.82/0.85  fof(f837,plain,(
% 3.82/0.85    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | (~spl6_6 | ~spl6_7 | ~spl6_18)),
% 3.82/0.85    inference(subsumption_resolution,[],[f836,f289])).
% 3.82/0.85  fof(f836,plain,(
% 3.82/0.85    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_6 | ~spl6_18)),
% 3.82/0.85    inference(subsumption_resolution,[],[f832,f192])).
% 3.82/0.85  fof(f832,plain,(
% 3.82/0.85    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_18),
% 3.82/0.85    inference(resolution,[],[f347,f113])).
% 3.82/0.85  fof(f113,plain,(
% 3.82/0.85    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.85    inference(cnf_transformation,[],[f47])).
% 3.82/0.85  fof(f818,plain,(
% 3.82/0.85    spl6_37 | ~spl6_7),
% 3.82/0.85    inference(avatar_split_clause,[],[f803,f287,f484])).
% 3.82/0.85  fof(f484,plain,(
% 3.82/0.85    spl6_37 <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 3.82/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 3.82/0.85  fof(f803,plain,(
% 3.82/0.85    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) | ~spl6_7),
% 3.82/0.85    inference(resolution,[],[f289,f106])).
% 3.82/0.85  fof(f106,plain,(
% 3.82/0.85    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.85    inference(cnf_transformation,[],[f40])).
% 3.82/0.85  fof(f40,plain,(
% 3.82/0.85    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.82/0.85    inference(ennf_transformation,[],[f14])).
% 3.82/0.85  fof(f14,axiom,(
% 3.82/0.85    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.82/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 3.82/0.85  fof(f437,plain,(
% 3.82/0.85    spl6_7 | ~spl6_3),
% 3.82/0.85    inference(avatar_split_clause,[],[f436,f175,f287])).
% 3.82/0.85  fof(f436,plain,(
% 3.82/0.85    v1_relat_1(sK1) | ~spl6_3),
% 3.82/0.85    inference(subsumption_resolution,[],[f285,f118])).
% 3.82/0.85  fof(f285,plain,(
% 3.82/0.85    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl6_3),
% 3.82/0.85    inference(resolution,[],[f177,f109])).
% 3.82/0.85  fof(f391,plain,(
% 3.82/0.85    spl6_18 | ~spl6_3 | ~spl6_4 | ~spl6_6),
% 3.82/0.85    inference(avatar_split_clause,[],[f390,f190,f180,f175,f345])).
% 3.82/0.85  fof(f390,plain,(
% 3.82/0.85    v2_funct_1(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_6)),
% 3.82/0.85    inference(subsumption_resolution,[],[f389,f192])).
% 3.82/0.85  fof(f389,plain,(
% 3.82/0.85    v2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl6_3 | ~spl6_4)),
% 3.82/0.85    inference(subsumption_resolution,[],[f262,f182])).
% 3.82/0.85  fof(f262,plain,(
% 3.82/0.85    v2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_3),
% 3.82/0.85    inference(resolution,[],[f177,f149])).
% 3.82/0.85  fof(f149,plain,(
% 3.82/0.85    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/0.85    inference(cnf_transformation,[],[f67])).
% 3.82/0.85  fof(f193,plain,(
% 3.82/0.85    spl6_6),
% 3.82/0.85    inference(avatar_split_clause,[],[f96,f190])).
% 3.82/0.85  fof(f96,plain,(
% 3.82/0.85    v1_funct_1(sK1)),
% 3.82/0.85    inference(cnf_transformation,[],[f81])).
% 3.82/0.85  fof(f81,plain,(
% 3.82/0.85    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.82/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f80])).
% 3.82/0.85  fof(f80,plain,(
% 3.82/0.85    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.82/0.85    introduced(choice_axiom,[])).
% 3.82/0.85  fof(f39,plain,(
% 3.82/0.85    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.82/0.85    inference(flattening,[],[f38])).
% 3.82/0.85  fof(f38,plain,(
% 3.82/0.85    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.82/0.85    inference(ennf_transformation,[],[f37])).
% 3.82/0.85  fof(f37,negated_conjecture,(
% 3.82/0.85    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.82/0.85    inference(negated_conjecture,[],[f36])).
% 3.82/0.85  fof(f36,conjecture,(
% 3.82/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.82/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 3.82/0.85  fof(f188,plain,(
% 3.82/0.85    spl6_5),
% 3.82/0.85    inference(avatar_split_clause,[],[f97,f185])).
% 3.82/0.85  fof(f97,plain,(
% 3.82/0.85    v1_funct_2(sK1,sK0,sK0)),
% 3.82/0.85    inference(cnf_transformation,[],[f81])).
% 3.82/0.85  fof(f183,plain,(
% 3.82/0.85    spl6_4),
% 3.82/0.85    inference(avatar_split_clause,[],[f98,f180])).
% 3.82/0.85  fof(f98,plain,(
% 3.82/0.85    v3_funct_2(sK1,sK0,sK0)),
% 3.82/0.85    inference(cnf_transformation,[],[f81])).
% 3.82/0.85  fof(f178,plain,(
% 3.82/0.85    spl6_3),
% 3.82/0.85    inference(avatar_split_clause,[],[f99,f175])).
% 3.82/0.85  fof(f99,plain,(
% 3.82/0.85    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.82/0.85    inference(cnf_transformation,[],[f81])).
% 3.82/0.85  fof(f173,plain,(
% 3.82/0.85    ~spl6_1 | ~spl6_2),
% 3.82/0.85    inference(avatar_split_clause,[],[f100,f170,f166])).
% 3.82/0.85  fof(f100,plain,(
% 3.82/0.85    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.82/0.85    inference(cnf_transformation,[],[f81])).
% 3.82/0.85  % SZS output end Proof for theBenchmark
% 3.82/0.85  % (13004)------------------------------
% 3.82/0.85  % (13004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.85  % (13004)Termination reason: Refutation
% 3.82/0.85  
% 3.82/0.85  % (13004)Memory used [KB]: 9850
% 3.82/0.85  % (13004)Time elapsed: 0.419 s
% 3.82/0.85  % (13004)------------------------------
% 3.82/0.85  % (13004)------------------------------
% 3.82/0.85  % (12974)Success in time 0.493 s
%------------------------------------------------------------------------------
