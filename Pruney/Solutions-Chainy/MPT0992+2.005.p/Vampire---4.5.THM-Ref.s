%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:10 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 384 expanded)
%              Number of leaves         :   49 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  622 (1356 expanded)
%              Number of equality atoms :  121 ( 310 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3525,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f119,f123,f127,f131,f135,f139,f221,f290,f472,f495,f505,f558,f575,f578,f597,f617,f631,f698,f713,f823,f832,f833,f834,f1881,f1913,f2002,f3524])).

fof(f3524,plain,
    ( spl5_91
    | spl5_45
    | ~ spl5_7
    | ~ spl5_23
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f3516,f1911,f493,f125,f818,f1908])).

fof(f1908,plain,
    ( spl5_91
  <=> ! [X3,X2] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f818,plain,
    ( spl5_45
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f125,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f493,plain,
    ( spl5_23
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1911,plain,
    ( spl5_92
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f3516,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_7
    | ~ spl5_23
    | ~ spl5_92 ),
    inference(resolution,[],[f3446,f2903])).

fof(f2903,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(resolution,[],[f1674,f126])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1674,plain,
    ( ! [X14,X17,X15,X18,X16] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X15)))
        | ~ m1_subset_1(k7_relat_1(sK3,X14),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15) )
    | ~ spl5_23 ),
    inference(resolution,[],[f265,f494])).

fof(f494,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f493])).

fof(f265,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X7)))
      | r1_tarski(k2_relat_1(X6),X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f177,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f84,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f3446,plain,
    ( ! [X15] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X15)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X15))) )
    | ~ spl5_92 ),
    inference(resolution,[],[f1912,f172])).

fof(f172,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f75,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
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

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1912,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f1911])).

fof(f2002,plain,
    ( ~ spl5_7
    | ~ spl5_23
    | ~ spl5_91 ),
    inference(avatar_contradiction_clause,[],[f1999])).

fof(f1999,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_23
    | ~ spl5_91 ),
    inference(subsumption_resolution,[],[f126,f1992])).

fof(f1992,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl5_23
    | ~ spl5_91 ),
    inference(resolution,[],[f1909,f494])).

fof(f1909,plain,
    ( ! [X2,X3] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f1908])).

fof(f1913,plain,
    ( spl5_91
    | spl5_92
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1901,f821,f1911,f1908])).

fof(f821,plain,
    ( spl5_46
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f1901,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl5_46 ),
    inference(superposition,[],[f394,f1876])).

fof(f1876,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f821])).

fof(f394,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r1_tarski(k1_relat_1(X6),X8)
      | ~ r1_tarski(k2_relat_1(X6),X7)
      | m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X7)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f81,f82])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f1881,plain,
    ( ~ spl5_7
    | ~ spl5_45
    | spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f951,f133,f110,f818,f125])).

fof(f110,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f133,plain,
    ( spl5_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f951,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_3
    | ~ spl5_9 ),
    inference(superposition,[],[f111,f457])).

fof(f457,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_9 ),
    inference(resolution,[],[f93,f134])).

fof(f134,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f111,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f834,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f833,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | v1_funct_2(k1_xboole_0,sK2,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f832,plain,
    ( ~ spl5_42
    | ~ spl5_6
    | ~ spl5_33
    | spl5_46 ),
    inference(avatar_split_clause,[],[f830,f821,f594,f121,f702])).

fof(f702,plain,
    ( spl5_42
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f121,plain,
    ( spl5_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f594,plain,
    ( spl5_33
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f830,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_33
    | spl5_46 ),
    inference(forward_demodulation,[],[f829,f595])).

fof(f595,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f594])).

fof(f829,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_46 ),
    inference(trivial_inequality_removal,[],[f828])).

fof(f828,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_46 ),
    inference(superposition,[],[f822,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f822,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl5_46 ),
    inference(avatar_component_clause,[],[f821])).

fof(f823,plain,
    ( ~ spl5_45
    | spl5_4
    | ~ spl5_46
    | spl5_22 ),
    inference(avatar_split_clause,[],[f808,f470,f821,f114,f818])).

fof(f114,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f470,plain,
    ( spl5_22
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f808,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_22 ),
    inference(resolution,[],[f645,f471])).

fof(f471,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f470])).

fof(f645,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relat_1(X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f642])).

fof(f642,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f87,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f713,plain,
    ( ~ spl5_7
    | spl5_42 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | ~ spl5_7
    | spl5_42 ),
    inference(subsumption_resolution,[],[f126,f710])).

fof(f710,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_42 ),
    inference(resolution,[],[f703,f82])).

fof(f703,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f702])).

fof(f698,plain,
    ( ~ spl5_41
    | spl5_22
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f670,f502,f470,f696])).

fof(f696,plain,
    ( spl5_41
  <=> v1_funct_2(k1_xboole_0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f502,plain,
    ( spl5_25
  <=> ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f670,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,sK1)
    | spl5_22
    | ~ spl5_25 ),
    inference(superposition,[],[f471,f660])).

fof(f660,plain,
    ( ! [X6] : k1_xboole_0 = k7_relat_1(sK3,X6)
    | ~ spl5_25 ),
    inference(resolution,[],[f503,f168])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f503,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f502])).

fof(f631,plain,
    ( spl5_38
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f621,f499,f629])).

fof(f629,plain,
    ( spl5_38
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f499,plain,
    ( spl5_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f621,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_24 ),
    inference(resolution,[],[f577,f168])).

fof(f577,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f499])).

fof(f617,plain,
    ( spl5_36
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f610,f573,f614])).

fof(f614,plain,
    ( spl5_36
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f573,plain,
    ( spl5_31
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f610,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_31 ),
    inference(resolution,[],[f574,f67])).

fof(f574,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f573])).

fof(f597,plain,
    ( ~ spl5_7
    | spl5_33
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f592,f556,f594,f125])).

fof(f556,plain,
    ( spl5_29
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f592,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_29 ),
    inference(superposition,[],[f83,f557])).

fof(f557,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f556])).

fof(f578,plain,
    ( spl5_24
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f576,f125,f117,f499])).

fof(f117,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f576,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f561,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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

fof(f561,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(superposition,[],[f126,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f575,plain,
    ( spl5_31
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f560,f121,f117,f573])).

fof(f560,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(superposition,[],[f122,f118])).

fof(f122,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f558,plain,
    ( ~ spl5_7
    | spl5_4
    | spl5_29
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f550,f129,f556,f114,f125])).

fof(f129,plain,
    ( spl5_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f550,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_8 ),
    inference(resolution,[],[f85,f130])).

fof(f130,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f505,plain,
    ( ~ spl5_24
    | spl5_25
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f497,f493,f502,f499])).

fof(f497,plain,
    ( ! [X3] :
        ( m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_23 ),
    inference(superposition,[],[f494,f97])).

fof(f495,plain,
    ( ~ spl5_9
    | spl5_23
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f491,f133,f493,f133])).

fof(f491,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f484])).

fof(f484,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_9 ),
    inference(superposition,[],[f95,f457])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f472,plain,
    ( ~ spl5_7
    | ~ spl5_22
    | spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f460,f133,f107,f470,f125])).

fof(f107,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f460,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_2
    | ~ spl5_9 ),
    inference(superposition,[],[f108,f457])).

fof(f108,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f290,plain,
    ( ~ spl5_9
    | ~ spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f287,f104,f125,f133])).

fof(f104,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f287,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl5_1 ),
    inference(resolution,[],[f94,f105])).

fof(f105,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f221,plain,
    ( spl5_15
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f216,f137,f219])).

fof(f219,plain,
    ( spl5_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f137,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f216,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(resolution,[],[f211,f181])).

fof(f181,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_10 ),
    inference(resolution,[],[f179,f74])).

fof(f179,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_10 ),
    inference(resolution,[],[f178,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f92,f138])).

fof(f138,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(global_subsumption,[],[f151,f210])).

fof(f210,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = X0
      | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f70,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(global_subsumption,[],[f151,f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f69,f67])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f151,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f68,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f64,f137])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f135,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f58,f133])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f47])).

% (10352)Time limit reached!
% (10352)------------------------------
% (10352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f131,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f127,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f60,f125])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f123,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f61,f121])).

fof(f61,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f119,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f62,f117,f114])).

fof(f62,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f112,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f63,f110,f107,f104])).

fof(f63,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:21:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (10376)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (10367)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (10356)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (10352)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (10366)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (10349)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (10346)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (10350)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (10347)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (10371)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (10377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (10379)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (10348)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10357)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (10370)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (10373)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10362)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (10365)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (10378)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (10354)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (10355)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (10369)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (10363)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (10368)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (10353)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (10364)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (10374)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (10358)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (10359)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (10360)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (10370)Refutation not found, incomplete strategy% (10370)------------------------------
% 0.22/0.56  % (10370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10370)Memory used [KB]: 10874
% 0.22/0.56  % (10370)Time elapsed: 0.103 s
% 0.22/0.56  % (10370)------------------------------
% 0.22/0.56  % (10370)------------------------------
% 2.59/0.73  % (10421)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.13/0.80  % (10367)Refutation found. Thanks to Tanya!
% 3.13/0.80  % SZS status Theorem for theBenchmark
% 3.13/0.81  % SZS output start Proof for theBenchmark
% 3.13/0.81  fof(f3525,plain,(
% 3.13/0.81    $false),
% 3.13/0.81    inference(avatar_sat_refutation,[],[f112,f119,f123,f127,f131,f135,f139,f221,f290,f472,f495,f505,f558,f575,f578,f597,f617,f631,f698,f713,f823,f832,f833,f834,f1881,f1913,f2002,f3524])).
% 3.13/0.81  fof(f3524,plain,(
% 3.13/0.81    spl5_91 | spl5_45 | ~spl5_7 | ~spl5_23 | ~spl5_92),
% 3.13/0.81    inference(avatar_split_clause,[],[f3516,f1911,f493,f125,f818,f1908])).
% 3.13/0.81  fof(f1908,plain,(
% 3.13/0.81    spl5_91 <=> ! [X3,X2] : ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 3.13/0.81  fof(f818,plain,(
% 3.13/0.81    spl5_45 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 3.13/0.81  fof(f125,plain,(
% 3.13/0.81    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.13/0.81  fof(f493,plain,(
% 3.13/0.81    spl5_23 <=> ! [X1,X0,X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 3.13/0.81  fof(f1911,plain,(
% 3.13/0.81    spl5_92 <=> ! [X1,X0] : (~r1_tarski(sK2,X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 3.13/0.81  fof(f3516,plain,(
% 3.13/0.81    ( ! [X0,X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_7 | ~spl5_23 | ~spl5_92)),
% 3.13/0.81    inference(resolution,[],[f3446,f2903])).
% 3.13/0.81  fof(f2903,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl5_7 | ~spl5_23)),
% 3.13/0.81    inference(resolution,[],[f1674,f126])).
% 3.13/0.81  fof(f126,plain,(
% 3.13/0.81    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 3.13/0.81    inference(avatar_component_clause,[],[f125])).
% 3.13/0.81  fof(f1674,plain,(
% 3.13/0.81    ( ! [X14,X17,X15,X18,X16] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X15))) | ~m1_subset_1(k7_relat_1(sK3,X14),k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15)) ) | ~spl5_23),
% 3.13/0.81    inference(resolution,[],[f265,f494])).
% 3.13/0.81  fof(f494,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_23),
% 3.13/0.81    inference(avatar_component_clause,[],[f493])).
% 3.13/0.81  fof(f265,plain,(
% 3.13/0.81    ( ! [X6,X10,X8,X7,X9] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X7))) | r1_tarski(k2_relat_1(X6),X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 3.13/0.81    inference(resolution,[],[f177,f82])).
% 3.13/0.81  fof(f82,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.81    inference(cnf_transformation,[],[f35])).
% 3.13/0.81  fof(f35,plain,(
% 3.13/0.81    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.81    inference(ennf_transformation,[],[f14])).
% 3.13/0.81  fof(f14,axiom,(
% 3.13/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.13/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.13/0.81  fof(f177,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.13/0.81    inference(resolution,[],[f84,f71])).
% 3.13/0.81  fof(f71,plain,(
% 3.13/0.81    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.13/0.81    inference(cnf_transformation,[],[f49])).
% 3.13/0.81  fof(f49,plain,(
% 3.13/0.81    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.13/0.81    inference(nnf_transformation,[],[f31])).
% 3.13/0.81  fof(f31,plain,(
% 3.13/0.81    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.13/0.81    inference(ennf_transformation,[],[f10])).
% 3.13/0.81  fof(f10,axiom,(
% 3.13/0.81    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.13/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 3.13/0.81  fof(f84,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.81    inference(cnf_transformation,[],[f37])).
% 3.13/0.81  fof(f37,plain,(
% 3.13/0.81    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.81    inference(ennf_transformation,[],[f23])).
% 3.13/0.81  fof(f23,plain,(
% 3.13/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.13/0.81    inference(pure_predicate_removal,[],[f15])).
% 3.13/0.81  fof(f15,axiom,(
% 3.13/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.13/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.13/0.81  fof(f3446,plain,(
% 3.13/0.81    ( ! [X15] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X15) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X15)))) ) | ~spl5_92),
% 3.13/0.81    inference(resolution,[],[f1912,f172])).
% 3.13/0.81  fof(f172,plain,(
% 3.13/0.81    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.13/0.81    inference(duplicate_literal_removal,[],[f171])).
% 3.13/0.81  fof(f171,plain,(
% 3.13/0.81    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 3.13/0.81    inference(resolution,[],[f75,f74])).
% 3.13/0.81  fof(f74,plain,(
% 3.13/0.81    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.13/0.81    inference(cnf_transformation,[],[f53])).
% 3.13/0.81  fof(f53,plain,(
% 3.13/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 3.13/0.81  fof(f52,plain,(
% 3.13/0.81    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.13/0.81    introduced(choice_axiom,[])).
% 3.13/0.81  fof(f51,plain,(
% 3.13/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/0.81    inference(rectify,[],[f50])).
% 3.13/0.81  fof(f50,plain,(
% 3.13/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/0.81    inference(nnf_transformation,[],[f32])).
% 3.13/0.81  fof(f32,plain,(
% 3.13/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.13/0.81    inference(ennf_transformation,[],[f1])).
% 3.13/0.81  fof(f1,axiom,(
% 3.13/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.13/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.13/0.81  fof(f75,plain,(
% 3.13/0.81    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.13/0.81    inference(cnf_transformation,[],[f53])).
% 3.13/0.81  fof(f1912,plain,(
% 3.13/0.81    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl5_92),
% 3.13/0.81    inference(avatar_component_clause,[],[f1911])).
% 3.13/0.81  fof(f2002,plain,(
% 3.13/0.81    ~spl5_7 | ~spl5_23 | ~spl5_91),
% 3.13/0.81    inference(avatar_contradiction_clause,[],[f1999])).
% 3.13/0.81  fof(f1999,plain,(
% 3.13/0.81    $false | (~spl5_7 | ~spl5_23 | ~spl5_91)),
% 3.13/0.81    inference(subsumption_resolution,[],[f126,f1992])).
% 3.13/0.81  fof(f1992,plain,(
% 3.13/0.81    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_23 | ~spl5_91)),
% 3.13/0.81    inference(resolution,[],[f1909,f494])).
% 3.13/0.81  fof(f1909,plain,(
% 3.13/0.81    ( ! [X2,X3] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl5_91),
% 3.13/0.81    inference(avatar_component_clause,[],[f1908])).
% 3.13/0.81  fof(f1913,plain,(
% 3.13/0.81    spl5_91 | spl5_92 | ~spl5_46),
% 3.13/0.81    inference(avatar_split_clause,[],[f1901,f821,f1911,f1908])).
% 3.13/0.81  fof(f821,plain,(
% 3.13/0.81    spl5_46 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 3.13/0.81  fof(f1901,plain,(
% 3.13/0.81    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl5_46),
% 3.13/0.81    inference(superposition,[],[f394,f1876])).
% 3.13/0.81  fof(f1876,plain,(
% 3.13/0.81    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl5_46),
% 3.13/0.81    inference(avatar_component_clause,[],[f821])).
% 3.13/0.81  fof(f394,plain,(
% 3.13/0.81    ( ! [X6,X10,X8,X7,X9] : (~r1_tarski(k1_relat_1(X6),X8) | ~r1_tarski(k2_relat_1(X6),X7) | m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X7))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 3.13/0.81    inference(resolution,[],[f81,f82])).
% 3.13/0.81  fof(f81,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.81    inference(cnf_transformation,[],[f34])).
% 3.13/0.81  fof(f34,plain,(
% 3.13/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.13/0.81    inference(flattening,[],[f33])).
% 3.13/0.81  fof(f33,plain,(
% 3.13/0.81    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.13/0.81    inference(ennf_transformation,[],[f17])).
% 3.13/0.81  fof(f17,axiom,(
% 3.13/0.81    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.13/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 3.13/0.81  fof(f1881,plain,(
% 3.13/0.81    ~spl5_7 | ~spl5_45 | spl5_3 | ~spl5_9),
% 3.13/0.81    inference(avatar_split_clause,[],[f951,f133,f110,f818,f125])).
% 3.13/0.81  fof(f110,plain,(
% 3.13/0.81    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.13/0.81  fof(f133,plain,(
% 3.13/0.81    spl5_9 <=> v1_funct_1(sK3)),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.13/0.81  fof(f951,plain,(
% 3.13/0.81    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl5_3 | ~spl5_9)),
% 3.13/0.81    inference(superposition,[],[f111,f457])).
% 3.13/0.81  fof(f457,plain,(
% 3.13/0.81    ( ! [X2,X0,X1] : (k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_9),
% 3.13/0.81    inference(resolution,[],[f93,f134])).
% 3.13/0.81  fof(f134,plain,(
% 3.13/0.81    v1_funct_1(sK3) | ~spl5_9),
% 3.13/0.81    inference(avatar_component_clause,[],[f133])).
% 3.13/0.81  fof(f93,plain,(
% 3.13/0.81    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 3.13/0.81    inference(cnf_transformation,[],[f44])).
% 3.13/0.81  fof(f44,plain,(
% 3.13/0.81    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.13/0.81    inference(flattening,[],[f43])).
% 3.13/0.81  fof(f43,plain,(
% 3.13/0.81    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.13/0.81    inference(ennf_transformation,[],[f20])).
% 3.13/0.81  fof(f20,axiom,(
% 3.13/0.81    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 3.13/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 3.13/0.81  fof(f111,plain,(
% 3.13/0.81    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 3.13/0.81    inference(avatar_component_clause,[],[f110])).
% 3.13/0.81  fof(f834,plain,(
% 3.13/0.81    k1_xboole_0 != sK3 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK3)),
% 3.13/0.81    introduced(theory_tautology_sat_conflict,[])).
% 3.13/0.81  fof(f833,plain,(
% 3.13/0.81    k1_xboole_0 != sK0 | k1_xboole_0 != sK3 | k1_xboole_0 != sK2 | v1_funct_2(k1_xboole_0,sK2,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 3.13/0.81    introduced(theory_tautology_sat_conflict,[])).
% 3.13/0.81  fof(f832,plain,(
% 3.13/0.81    ~spl5_42 | ~spl5_6 | ~spl5_33 | spl5_46),
% 3.13/0.81    inference(avatar_split_clause,[],[f830,f821,f594,f121,f702])).
% 3.13/0.81  fof(f702,plain,(
% 3.13/0.81    spl5_42 <=> v1_relat_1(sK3)),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 3.13/0.81  fof(f121,plain,(
% 3.13/0.81    spl5_6 <=> r1_tarski(sK2,sK0)),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.13/0.81  fof(f594,plain,(
% 3.13/0.81    spl5_33 <=> sK0 = k1_relat_1(sK3)),
% 3.13/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 3.13/0.81  fof(f830,plain,(
% 3.13/0.81    ~r1_tarski(sK2,sK0) | ~v1_relat_1(sK3) | (~spl5_33 | spl5_46)),
% 3.13/0.81    inference(forward_demodulation,[],[f829,f595])).
% 3.13/0.81  fof(f595,plain,(
% 3.13/0.81    sK0 = k1_relat_1(sK3) | ~spl5_33),
% 3.13/0.81    inference(avatar_component_clause,[],[f594])).
% 3.13/0.81  fof(f829,plain,(
% 3.13/0.81    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_46),
% 3.13/0.81    inference(trivial_inequality_removal,[],[f828])).
% 3.13/0.81  fof(f828,plain,(
% 3.13/0.81    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_46),
% 3.13/0.81    inference(superposition,[],[f822,f70])).
% 3.13/0.81  fof(f70,plain,(
% 3.13/0.81    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.13/0.81    inference(cnf_transformation,[],[f30])).
% 3.13/0.81  fof(f30,plain,(
% 3.13/0.81    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.13/0.81    inference(flattening,[],[f29])).
% 3.13/0.82  fof(f29,plain,(
% 3.13/0.82    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.13/0.82    inference(ennf_transformation,[],[f13])).
% 3.13/0.82  fof(f13,axiom,(
% 3.13/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 3.13/0.82  fof(f822,plain,(
% 3.13/0.82    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl5_46),
% 3.13/0.82    inference(avatar_component_clause,[],[f821])).
% 3.13/0.82  fof(f823,plain,(
% 3.13/0.82    ~spl5_45 | spl5_4 | ~spl5_46 | spl5_22),
% 3.13/0.82    inference(avatar_split_clause,[],[f808,f470,f821,f114,f818])).
% 3.13/0.82  fof(f114,plain,(
% 3.13/0.82    spl5_4 <=> k1_xboole_0 = sK1),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.13/0.82  fof(f470,plain,(
% 3.13/0.82    spl5_22 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.13/0.82  fof(f808,plain,(
% 3.13/0.82    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_22),
% 3.13/0.82    inference(resolution,[],[f645,f471])).
% 3.13/0.82  fof(f471,plain,(
% 3.13/0.82    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl5_22),
% 3.13/0.82    inference(avatar_component_clause,[],[f470])).
% 3.13/0.82  fof(f645,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f642])).
% 3.13/0.82  fof(f642,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.82    inference(superposition,[],[f87,f83])).
% 3.13/0.82  fof(f83,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.82    inference(cnf_transformation,[],[f36])).
% 3.13/0.82  fof(f36,plain,(
% 3.13/0.82    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.82    inference(ennf_transformation,[],[f16])).
% 3.13/0.82  fof(f16,axiom,(
% 3.13/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.13/0.82  fof(f87,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.82    inference(cnf_transformation,[],[f57])).
% 3.13/0.82  fof(f57,plain,(
% 3.13/0.82    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.82    inference(nnf_transformation,[],[f39])).
% 3.13/0.82  fof(f39,plain,(
% 3.13/0.82    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.82    inference(flattening,[],[f38])).
% 3.13/0.82  fof(f38,plain,(
% 3.13/0.82    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/0.82    inference(ennf_transformation,[],[f18])).
% 3.13/0.82  fof(f18,axiom,(
% 3.13/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 3.13/0.82  fof(f713,plain,(
% 3.13/0.82    ~spl5_7 | spl5_42),
% 3.13/0.82    inference(avatar_contradiction_clause,[],[f712])).
% 3.13/0.82  fof(f712,plain,(
% 3.13/0.82    $false | (~spl5_7 | spl5_42)),
% 3.13/0.82    inference(subsumption_resolution,[],[f126,f710])).
% 3.13/0.82  fof(f710,plain,(
% 3.13/0.82    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_42),
% 3.13/0.82    inference(resolution,[],[f703,f82])).
% 3.13/0.82  fof(f703,plain,(
% 3.13/0.82    ~v1_relat_1(sK3) | spl5_42),
% 3.13/0.82    inference(avatar_component_clause,[],[f702])).
% 3.13/0.82  fof(f698,plain,(
% 3.13/0.82    ~spl5_41 | spl5_22 | ~spl5_25),
% 3.13/0.82    inference(avatar_split_clause,[],[f670,f502,f470,f696])).
% 3.13/0.82  fof(f696,plain,(
% 3.13/0.82    spl5_41 <=> v1_funct_2(k1_xboole_0,sK2,sK1)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 3.13/0.82  fof(f502,plain,(
% 3.13/0.82    spl5_25 <=> ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.13/0.82  fof(f670,plain,(
% 3.13/0.82    ~v1_funct_2(k1_xboole_0,sK2,sK1) | (spl5_22 | ~spl5_25)),
% 3.13/0.82    inference(superposition,[],[f471,f660])).
% 3.13/0.82  fof(f660,plain,(
% 3.13/0.82    ( ! [X6] : (k1_xboole_0 = k7_relat_1(sK3,X6)) ) | ~spl5_25),
% 3.13/0.82    inference(resolution,[],[f503,f168])).
% 3.13/0.82  fof(f168,plain,(
% 3.13/0.82    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 3.13/0.82    inference(resolution,[],[f76,f67])).
% 3.13/0.82  fof(f67,plain,(
% 3.13/0.82    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.13/0.82    inference(cnf_transformation,[],[f27])).
% 3.13/0.82  fof(f27,plain,(
% 3.13/0.82    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.13/0.82    inference(ennf_transformation,[],[f3])).
% 3.13/0.82  fof(f3,axiom,(
% 3.13/0.82    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 3.13/0.82  fof(f76,plain,(
% 3.13/0.82    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.13/0.82    inference(cnf_transformation,[],[f54])).
% 3.13/0.82  fof(f54,plain,(
% 3.13/0.82    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.13/0.82    inference(nnf_transformation,[],[f6])).
% 3.13/0.82  fof(f6,axiom,(
% 3.13/0.82    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.13/0.82  fof(f503,plain,(
% 3.13/0.82    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_25),
% 3.13/0.82    inference(avatar_component_clause,[],[f502])).
% 3.13/0.82  fof(f631,plain,(
% 3.13/0.82    spl5_38 | ~spl5_24),
% 3.13/0.82    inference(avatar_split_clause,[],[f621,f499,f629])).
% 3.13/0.82  fof(f629,plain,(
% 3.13/0.82    spl5_38 <=> k1_xboole_0 = sK3),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 3.13/0.82  fof(f499,plain,(
% 3.13/0.82    spl5_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 3.13/0.82  fof(f621,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | ~spl5_24),
% 3.13/0.82    inference(resolution,[],[f577,f168])).
% 3.13/0.82  fof(f577,plain,(
% 3.13/0.82    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_24),
% 3.13/0.82    inference(avatar_component_clause,[],[f499])).
% 3.13/0.82  fof(f617,plain,(
% 3.13/0.82    spl5_36 | ~spl5_31),
% 3.13/0.82    inference(avatar_split_clause,[],[f610,f573,f614])).
% 3.13/0.82  fof(f614,plain,(
% 3.13/0.82    spl5_36 <=> k1_xboole_0 = sK2),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 3.13/0.82  fof(f573,plain,(
% 3.13/0.82    spl5_31 <=> r1_tarski(sK2,k1_xboole_0)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 3.13/0.82  fof(f610,plain,(
% 3.13/0.82    k1_xboole_0 = sK2 | ~spl5_31),
% 3.13/0.82    inference(resolution,[],[f574,f67])).
% 3.13/0.82  fof(f574,plain,(
% 3.13/0.82    r1_tarski(sK2,k1_xboole_0) | ~spl5_31),
% 3.13/0.82    inference(avatar_component_clause,[],[f573])).
% 3.13/0.82  fof(f597,plain,(
% 3.13/0.82    ~spl5_7 | spl5_33 | ~spl5_29),
% 3.13/0.82    inference(avatar_split_clause,[],[f592,f556,f594,f125])).
% 3.13/0.82  fof(f556,plain,(
% 3.13/0.82    spl5_29 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 3.13/0.82  fof(f592,plain,(
% 3.13/0.82    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_29),
% 3.13/0.82    inference(superposition,[],[f83,f557])).
% 3.13/0.82  fof(f557,plain,(
% 3.13/0.82    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_29),
% 3.13/0.82    inference(avatar_component_clause,[],[f556])).
% 3.13/0.82  fof(f578,plain,(
% 3.13/0.82    spl5_24 | ~spl5_5 | ~spl5_7),
% 3.13/0.82    inference(avatar_split_clause,[],[f576,f125,f117,f499])).
% 3.13/0.82  fof(f117,plain,(
% 3.13/0.82    spl5_5 <=> k1_xboole_0 = sK0),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.13/0.82  fof(f576,plain,(
% 3.13/0.82    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_5 | ~spl5_7)),
% 3.13/0.82    inference(forward_demodulation,[],[f561,f97])).
% 3.13/0.82  fof(f97,plain,(
% 3.13/0.82    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.13/0.82    inference(equality_resolution,[],[f79])).
% 3.13/0.82  fof(f79,plain,(
% 3.13/0.82    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.13/0.82    inference(cnf_transformation,[],[f56])).
% 3.13/0.82  fof(f56,plain,(
% 3.13/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/0.82    inference(flattening,[],[f55])).
% 3.13/0.82  fof(f55,plain,(
% 3.13/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/0.82    inference(nnf_transformation,[],[f4])).
% 3.13/0.82  fof(f4,axiom,(
% 3.13/0.82    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.13/0.82  fof(f561,plain,(
% 3.13/0.82    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_5 | ~spl5_7)),
% 3.13/0.82    inference(superposition,[],[f126,f118])).
% 3.13/0.82  fof(f118,plain,(
% 3.13/0.82    k1_xboole_0 = sK0 | ~spl5_5),
% 3.13/0.82    inference(avatar_component_clause,[],[f117])).
% 3.13/0.82  fof(f575,plain,(
% 3.13/0.82    spl5_31 | ~spl5_5 | ~spl5_6),
% 3.13/0.82    inference(avatar_split_clause,[],[f560,f121,f117,f573])).
% 3.13/0.82  fof(f560,plain,(
% 3.13/0.82    r1_tarski(sK2,k1_xboole_0) | (~spl5_5 | ~spl5_6)),
% 3.13/0.82    inference(superposition,[],[f122,f118])).
% 3.13/0.82  fof(f122,plain,(
% 3.13/0.82    r1_tarski(sK2,sK0) | ~spl5_6),
% 3.13/0.82    inference(avatar_component_clause,[],[f121])).
% 3.13/0.82  fof(f558,plain,(
% 3.13/0.82    ~spl5_7 | spl5_4 | spl5_29 | ~spl5_8),
% 3.13/0.82    inference(avatar_split_clause,[],[f550,f129,f556,f114,f125])).
% 3.13/0.82  fof(f129,plain,(
% 3.13/0.82    spl5_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.13/0.82  fof(f550,plain,(
% 3.13/0.82    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_8),
% 3.13/0.82    inference(resolution,[],[f85,f130])).
% 3.13/0.82  fof(f130,plain,(
% 3.13/0.82    v1_funct_2(sK3,sK0,sK1) | ~spl5_8),
% 3.13/0.82    inference(avatar_component_clause,[],[f129])).
% 3.13/0.82  fof(f85,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/0.82    inference(cnf_transformation,[],[f57])).
% 3.13/0.82  fof(f505,plain,(
% 3.13/0.82    ~spl5_24 | spl5_25 | ~spl5_23),
% 3.13/0.82    inference(avatar_split_clause,[],[f497,f493,f502,f499])).
% 3.13/0.82  fof(f497,plain,(
% 3.13/0.82    ( ! [X3] : (m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_23),
% 3.13/0.82    inference(superposition,[],[f494,f97])).
% 3.13/0.82  fof(f495,plain,(
% 3.13/0.82    ~spl5_9 | spl5_23 | ~spl5_9),
% 3.13/0.82    inference(avatar_split_clause,[],[f491,f133,f493,f133])).
% 3.13/0.82  fof(f491,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3)) ) | ~spl5_9),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f484])).
% 3.13/0.82  fof(f484,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_9),
% 3.13/0.82    inference(superposition,[],[f95,f457])).
% 3.13/0.82  fof(f95,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f46])).
% 3.13/0.82  fof(f46,plain,(
% 3.13/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.13/0.82    inference(flattening,[],[f45])).
% 3.13/0.82  fof(f45,plain,(
% 3.13/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.13/0.82    inference(ennf_transformation,[],[f19])).
% 3.13/0.82  fof(f19,axiom,(
% 3.13/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 3.13/0.82  fof(f472,plain,(
% 3.13/0.82    ~spl5_7 | ~spl5_22 | spl5_2 | ~spl5_9),
% 3.13/0.82    inference(avatar_split_clause,[],[f460,f133,f107,f470,f125])).
% 3.13/0.82  fof(f107,plain,(
% 3.13/0.82    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.13/0.82  fof(f460,plain,(
% 3.13/0.82    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl5_2 | ~spl5_9)),
% 3.13/0.82    inference(superposition,[],[f108,f457])).
% 3.13/0.82  fof(f108,plain,(
% 3.13/0.82    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl5_2),
% 3.13/0.82    inference(avatar_component_clause,[],[f107])).
% 3.13/0.82  fof(f290,plain,(
% 3.13/0.82    ~spl5_9 | ~spl5_7 | spl5_1),
% 3.13/0.82    inference(avatar_split_clause,[],[f287,f104,f125,f133])).
% 3.13/0.82  fof(f104,plain,(
% 3.13/0.82    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.13/0.82  fof(f287,plain,(
% 3.13/0.82    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl5_1),
% 3.13/0.82    inference(resolution,[],[f94,f105])).
% 3.13/0.82  fof(f105,plain,(
% 3.13/0.82    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl5_1),
% 3.13/0.82    inference(avatar_component_clause,[],[f104])).
% 3.13/0.82  fof(f94,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f46])).
% 3.13/0.82  fof(f221,plain,(
% 3.13/0.82    spl5_15 | ~spl5_10),
% 3.13/0.82    inference(avatar_split_clause,[],[f216,f137,f219])).
% 3.13/0.82  fof(f219,plain,(
% 3.13/0.82    spl5_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.13/0.82  fof(f137,plain,(
% 3.13/0.82    spl5_10 <=> v1_xboole_0(k1_xboole_0)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.13/0.82  fof(f216,plain,(
% 3.13/0.82    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_10),
% 3.13/0.82    inference(resolution,[],[f211,f181])).
% 3.13/0.82  fof(f181,plain,(
% 3.13/0.82    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl5_10),
% 3.13/0.82    inference(resolution,[],[f179,f74])).
% 3.13/0.82  fof(f179,plain,(
% 3.13/0.82    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_10),
% 3.13/0.82    inference(resolution,[],[f178,f65])).
% 3.13/0.82  fof(f65,plain,(
% 3.13/0.82    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.13/0.82    inference(cnf_transformation,[],[f5])).
% 3.13/0.82  fof(f5,axiom,(
% 3.13/0.82    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.13/0.82  fof(f178,plain,(
% 3.13/0.82    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl5_10),
% 3.13/0.82    inference(resolution,[],[f92,f138])).
% 3.13/0.82  fof(f138,plain,(
% 3.13/0.82    v1_xboole_0(k1_xboole_0) | ~spl5_10),
% 3.13/0.82    inference(avatar_component_clause,[],[f137])).
% 3.13/0.82  fof(f92,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f42])).
% 3.13/0.82  fof(f42,plain,(
% 3.13/0.82    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.13/0.82    inference(ennf_transformation,[],[f8])).
% 3.13/0.82  fof(f8,axiom,(
% 3.13/0.82    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 3.13/0.82  fof(f211,plain,(
% 3.13/0.82    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X0) )),
% 3.13/0.82    inference(global_subsumption,[],[f151,f210])).
% 3.13/0.82  fof(f210,plain,(
% 3.13/0.82    ( ! [X0] : (k1_relat_1(k1_xboole_0) = X0 | ~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 3.13/0.82    inference(superposition,[],[f70,f160])).
% 3.13/0.82  fof(f160,plain,(
% 3.13/0.82    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 3.13/0.82    inference(global_subsumption,[],[f151,f159])).
% 3.13/0.82  fof(f159,plain,(
% 3.13/0.82    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 3.13/0.82    inference(resolution,[],[f69,f67])).
% 3.13/0.82  fof(f69,plain,(
% 3.13/0.82    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f28])).
% 3.13/0.82  fof(f28,plain,(
% 3.13/0.82    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.13/0.82    inference(ennf_transformation,[],[f12])).
% 3.13/0.82  fof(f12,axiom,(
% 3.13/0.82    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 3.13/0.82  fof(f151,plain,(
% 3.13/0.82    v1_relat_1(k1_xboole_0)),
% 3.13/0.82    inference(superposition,[],[f68,f96])).
% 3.13/0.82  fof(f96,plain,(
% 3.13/0.82    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.13/0.82    inference(equality_resolution,[],[f80])).
% 3.13/0.82  fof(f80,plain,(
% 3.13/0.82    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.13/0.82    inference(cnf_transformation,[],[f56])).
% 3.13/0.82  fof(f68,plain,(
% 3.13/0.82    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.13/0.82    inference(cnf_transformation,[],[f11])).
% 3.13/0.82  fof(f11,axiom,(
% 3.13/0.82    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.13/0.82  fof(f139,plain,(
% 3.13/0.82    spl5_10),
% 3.13/0.82    inference(avatar_split_clause,[],[f64,f137])).
% 3.13/0.82  fof(f64,plain,(
% 3.13/0.82    v1_xboole_0(k1_xboole_0)),
% 3.13/0.82    inference(cnf_transformation,[],[f2])).
% 3.13/0.82  fof(f2,axiom,(
% 3.13/0.82    v1_xboole_0(k1_xboole_0)),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.13/0.82  fof(f135,plain,(
% 3.13/0.82    spl5_9),
% 3.13/0.82    inference(avatar_split_clause,[],[f58,f133])).
% 3.13/0.82  fof(f58,plain,(
% 3.13/0.82    v1_funct_1(sK3)),
% 3.13/0.82    inference(cnf_transformation,[],[f48])).
% 3.13/0.82  fof(f48,plain,(
% 3.13/0.82    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.13/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f47])).
% 3.13/0.82  % (10352)Time limit reached!
% 3.13/0.82  % (10352)------------------------------
% 3.13/0.82  % (10352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  fof(f47,plain,(
% 3.13/0.82    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.13/0.82    introduced(choice_axiom,[])).
% 3.13/0.82  fof(f25,plain,(
% 3.13/0.82    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.13/0.82    inference(flattening,[],[f24])).
% 3.13/0.82  fof(f24,plain,(
% 3.13/0.82    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.13/0.82    inference(ennf_transformation,[],[f22])).
% 3.13/0.82  fof(f22,negated_conjecture,(
% 3.13/0.82    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.13/0.82    inference(negated_conjecture,[],[f21])).
% 3.13/0.82  fof(f21,conjecture,(
% 3.13/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 3.13/0.82  fof(f131,plain,(
% 3.13/0.82    spl5_8),
% 3.13/0.82    inference(avatar_split_clause,[],[f59,f129])).
% 3.13/0.82  fof(f59,plain,(
% 3.13/0.82    v1_funct_2(sK3,sK0,sK1)),
% 3.13/0.82    inference(cnf_transformation,[],[f48])).
% 3.13/0.82  fof(f127,plain,(
% 3.13/0.82    spl5_7),
% 3.13/0.82    inference(avatar_split_clause,[],[f60,f125])).
% 3.13/0.82  fof(f60,plain,(
% 3.13/0.82    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.13/0.82    inference(cnf_transformation,[],[f48])).
% 3.13/0.82  fof(f123,plain,(
% 3.13/0.82    spl5_6),
% 3.13/0.82    inference(avatar_split_clause,[],[f61,f121])).
% 3.13/0.82  fof(f61,plain,(
% 3.13/0.82    r1_tarski(sK2,sK0)),
% 3.13/0.82    inference(cnf_transformation,[],[f48])).
% 3.13/0.82  fof(f119,plain,(
% 3.13/0.82    ~spl5_4 | spl5_5),
% 3.13/0.82    inference(avatar_split_clause,[],[f62,f117,f114])).
% 3.13/0.82  fof(f62,plain,(
% 3.13/0.82    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.13/0.82    inference(cnf_transformation,[],[f48])).
% 3.13/0.82  fof(f112,plain,(
% 3.13/0.82    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 3.13/0.82    inference(avatar_split_clause,[],[f63,f110,f107,f104])).
% 3.13/0.82  fof(f63,plain,(
% 3.13/0.82    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.13/0.82    inference(cnf_transformation,[],[f48])).
% 3.13/0.82  % SZS output end Proof for theBenchmark
% 3.13/0.82  % (10367)------------------------------
% 3.13/0.82  % (10367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (10367)Termination reason: Refutation
% 3.13/0.82  
% 3.13/0.82  % (10367)Memory used [KB]: 12665
% 3.13/0.82  % (10367)Time elapsed: 0.385 s
% 3.13/0.82  % (10367)------------------------------
% 3.13/0.82  % (10367)------------------------------
% 3.13/0.82  % (10341)Success in time 0.458 s
%------------------------------------------------------------------------------
