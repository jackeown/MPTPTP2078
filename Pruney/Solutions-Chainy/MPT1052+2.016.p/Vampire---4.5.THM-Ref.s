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
% DateTime   : Thu Dec  3 13:07:05 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 321 expanded)
%              Number of leaves         :   47 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :  482 ( 802 expanded)
%              Number of equality atoms :  106 ( 203 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f976,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f104,f109,f114,f119,f242,f268,f312,f474,f480,f509,f535,f581,f662,f666,f689,f709,f714,f716,f796,f812,f813,f823,f824,f825,f869,f927,f942,f975])).

fof(f975,plain,(
    spl5_65 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | spl5_65 ),
    inference(resolution,[],[f792,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f792,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl5_65 ),
    inference(avatar_component_clause,[],[f790])).

fof(f790,plain,
    ( spl5_65
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f942,plain,
    ( ~ spl5_65
    | spl5_3
    | ~ spl5_6
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f941,f596,f111,f97,f790])).

fof(f97,plain,
    ( spl5_3
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f111,plain,
    ( spl5_6
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f596,plain,
    ( spl5_51
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f941,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f787,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f787,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | spl5_3
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f99,f598])).

fof(f598,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f596])).

fof(f99,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f927,plain,
    ( spl5_51
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f922,f413,f106,f596])).

fof(f106,plain,
    ( spl5_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f413,plain,
    ( spl5_39
  <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f922,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(superposition,[],[f136,f415])).

fof(f415,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f413])).

fof(f136,plain,
    ( ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl5_5 ),
    inference(resolution,[],[f56,f134])).

fof(f134,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_5 ),
    inference(resolution,[],[f133,f108])).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f869,plain,
    ( ~ spl5_31
    | spl5_41
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f868,f334,f444,f340])).

fof(f340,plain,
    ( spl5_31
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f444,plain,
    ( spl5_41
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f334,plain,
    ( spl5_30
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f868,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_30 ),
    inference(resolution,[],[f336,f243])).

fof(f243,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f336,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f334])).

fof(f825,plain,
    ( ~ spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f822,f87,f147])).

fof(f147,plain,
    ( spl5_9
  <=> v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f87,plain,
    ( spl5_1
  <=> r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f822,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | ~ spl5_1 ),
    inference(resolution,[],[f89,f48])).

fof(f89,plain,
    ( r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f824,plain,
    ( spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f820,f87,f198])).

fof(f198,plain,
    ( spl5_10
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f820,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f89,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f823,plain,
    ( spl5_13
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f819,f87,f227])).

fof(f227,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f819,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1 ),
    inference(resolution,[],[f89,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f67,f50])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f813,plain,
    ( spl5_31
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f807,f351,f340])).

fof(f351,plain,
    ( spl5_33
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f807,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_33 ),
    inference(resolution,[],[f353,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f353,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f351])).

fof(f812,plain,
    ( spl5_39
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f806,f351,f413])).

fof(f806,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_33 ),
    inference(resolution,[],[f353,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f796,plain,
    ( spl5_33
    | ~ spl5_15
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f349,f305,f239,f351])).

fof(f239,plain,
    ( spl5_15
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f305,plain,
    ( spl5_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f349,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f321,f80])).

fof(f321,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl5_15
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f241,f307])).

fof(f307,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f305])).

fof(f241,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f239])).

fof(f716,plain,
    ( k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f714,plain,
    ( spl5_26
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f713,f706,f305])).

fof(f706,plain,
    ( spl5_59
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f713,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_59 ),
    inference(resolution,[],[f708,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f708,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f706])).

fof(f709,plain,
    ( spl5_59
    | ~ spl5_5
    | spl5_42 ),
    inference(avatar_split_clause,[],[f704,f465,f106,f706])).

fof(f465,plain,
    ( spl5_42
  <=> v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f704,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_5
    | spl5_42 ),
    inference(resolution,[],[f467,f184])).

fof(f184,plain,
    ( ! [X0] :
        ( v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f108])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f467,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))
    | spl5_42 ),
    inference(avatar_component_clause,[],[f465])).

fof(f689,plain,
    ( ~ spl5_42
    | spl5_9
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f688,f309,f147,f465])).

fof(f309,plain,
    ( spl5_27
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f688,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))
    | spl5_9
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f149,f311])).

fof(f311,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f149,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f666,plain,
    ( ~ spl5_7
    | spl5_57 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl5_7
    | spl5_57 ),
    inference(resolution,[],[f661,f315])).

fof(f315,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f314])).

fof(f314,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f313,f192])).

fof(f192,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f189,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_7
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f189,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f68,f129])).

fof(f129,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f57,f43])).

% (21702)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f313,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f270,f129])).

fof(f270,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f82,f80])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f661,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_57 ),
    inference(avatar_component_clause,[],[f659])).

fof(f659,plain,
    ( spl5_57
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f662,plain,
    ( ~ spl5_57
    | spl5_50
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f657,f596,f578,f659])).

fof(f578,plain,
    ( spl5_50
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f657,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_50
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f580,f598])).

fof(f580,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl5_50 ),
    inference(avatar_component_clause,[],[f578])).

fof(f581,plain,
    ( ~ spl5_50
    | ~ spl5_27
    | spl5_30 ),
    inference(avatar_split_clause,[],[f576,f334,f309,f578])).

fof(f576,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_27
    | spl5_30 ),
    inference(forward_demodulation,[],[f335,f311])).

fof(f335,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,sK1)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f334])).

fof(f535,plain,
    ( spl5_33
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f534,f309,f239,f351])).

fof(f534,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f522,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f522,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(backward_demodulation,[],[f241,f311])).

fof(f509,plain,
    ( ~ spl5_10
    | spl5_27
    | spl5_4
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f508,f234,f227,f101,f309,f198])).

fof(f101,plain,
    ( spl5_4
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f234,plain,
    ( spl5_14
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f508,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f504,f236])).

fof(f236,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f234])).

fof(f504,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f74,f229])).

fof(f229,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f227])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f480,plain,
    ( spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f478,f227,f234])).

fof(f478,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_13 ),
    inference(resolution,[],[f229,f68])).

fof(f474,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f470,f239,f253,f92,f249])).

fof(f249,plain,
    ( spl5_16
  <=> r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f92,plain,
    ( spl5_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f253,plain,
    ( spl5_17
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f470,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_15 ),
    inference(resolution,[],[f241,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f312,plain,
    ( spl5_26
    | spl5_27
    | spl5_3
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f275,f249,f97,f309,f305])).

fof(f275,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_16 ),
    inference(superposition,[],[f251,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f251,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f249])).

fof(f268,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f255,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f255,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f253])).

fof(f242,plain,
    ( spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f232,f227,f239])).

fof(f232,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_13 ),
    inference(resolution,[],[f229,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f119,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f41,f116])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f114,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f42,f111])).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f40,f106])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f104,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f37,f101,f97])).

fof(f37,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f95,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f75,f87])).

fof(f75,plain,(
    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f39,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (21704)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (21721)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (21721)Refutation not found, incomplete strategy% (21721)------------------------------
% 0.20/0.49  % (21721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21721)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21721)Memory used [KB]: 10874
% 0.20/0.50  % (21721)Time elapsed: 0.073 s
% 0.20/0.50  % (21721)------------------------------
% 0.20/0.50  % (21721)------------------------------
% 0.20/0.52  % (21701)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (21715)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.54  % (21711)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.56  % (21718)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.56  % (21699)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.57  % (21728)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.57  % (21714)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.57  % (21703)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.57  % (21710)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.58  % (21722)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.58  % (21725)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.58  % (21713)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.58  % (21716)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.58  % (21720)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.58  % (21715)Refutation found. Thanks to Tanya!
% 1.44/0.58  % SZS status Theorem for theBenchmark
% 1.44/0.58  % SZS output start Proof for theBenchmark
% 1.44/0.58  fof(f976,plain,(
% 1.44/0.58    $false),
% 1.44/0.58    inference(avatar_sat_refutation,[],[f90,f95,f104,f109,f114,f119,f242,f268,f312,f474,f480,f509,f535,f581,f662,f666,f689,f709,f714,f716,f796,f812,f813,f823,f824,f825,f869,f927,f942,f975])).
% 1.44/0.58  fof(f975,plain,(
% 1.44/0.58    spl5_65),
% 1.44/0.58    inference(avatar_contradiction_clause,[],[f974])).
% 1.44/0.58  fof(f974,plain,(
% 1.44/0.58    $false | spl5_65),
% 1.44/0.58    inference(resolution,[],[f792,f43])).
% 1.44/0.58  fof(f43,plain,(
% 1.44/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f6])).
% 1.44/0.58  fof(f6,axiom,(
% 1.44/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.58  fof(f792,plain,(
% 1.44/0.58    ~r1_tarski(k1_xboole_0,sK1) | spl5_65),
% 1.44/0.58    inference(avatar_component_clause,[],[f790])).
% 1.44/0.58  fof(f790,plain,(
% 1.44/0.58    spl5_65 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 1.44/0.58  fof(f942,plain,(
% 1.44/0.58    ~spl5_65 | spl5_3 | ~spl5_6 | ~spl5_51),
% 1.44/0.58    inference(avatar_split_clause,[],[f941,f596,f111,f97,f790])).
% 1.44/0.58  fof(f97,plain,(
% 1.44/0.58    spl5_3 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.44/0.58  fof(f111,plain,(
% 1.44/0.58    spl5_6 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.44/0.58  fof(f596,plain,(
% 1.44/0.58    spl5_51 <=> k1_xboole_0 = sK2),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.44/0.58  fof(f941,plain,(
% 1.44/0.58    ~r1_tarski(k1_xboole_0,sK1) | (spl5_3 | ~spl5_6 | ~spl5_51)),
% 1.44/0.58    inference(forward_demodulation,[],[f787,f113])).
% 1.44/0.58  fof(f113,plain,(
% 1.44/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_6),
% 1.44/0.58    inference(avatar_component_clause,[],[f111])).
% 1.44/0.58  fof(f787,plain,(
% 1.44/0.58    ~r1_tarski(k2_relat_1(k1_xboole_0),sK1) | (spl5_3 | ~spl5_51)),
% 1.44/0.58    inference(forward_demodulation,[],[f99,f598])).
% 1.44/0.58  fof(f598,plain,(
% 1.44/0.58    k1_xboole_0 = sK2 | ~spl5_51),
% 1.44/0.58    inference(avatar_component_clause,[],[f596])).
% 1.44/0.58  fof(f99,plain,(
% 1.44/0.58    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_3),
% 1.44/0.58    inference(avatar_component_clause,[],[f97])).
% 1.44/0.58  fof(f927,plain,(
% 1.44/0.58    spl5_51 | ~spl5_5 | ~spl5_39),
% 1.44/0.58    inference(avatar_split_clause,[],[f922,f413,f106,f596])).
% 1.44/0.58  fof(f106,plain,(
% 1.44/0.58    spl5_5 <=> v1_xboole_0(k1_xboole_0)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.44/0.58  fof(f413,plain,(
% 1.44/0.58    spl5_39 <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.44/0.58  fof(f922,plain,(
% 1.44/0.58    k1_xboole_0 = sK2 | (~spl5_5 | ~spl5_39)),
% 1.44/0.58    inference(superposition,[],[f136,f415])).
% 1.44/0.58  fof(f415,plain,(
% 1.44/0.58    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) | ~spl5_39),
% 1.44/0.58    inference(avatar_component_clause,[],[f413])).
% 1.44/0.58  fof(f136,plain,(
% 1.44/0.58    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl5_5),
% 1.44/0.58    inference(resolution,[],[f56,f134])).
% 1.44/0.58  fof(f134,plain,(
% 1.44/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_5),
% 1.44/0.58    inference(resolution,[],[f133,f108])).
% 1.44/0.58  fof(f108,plain,(
% 1.44/0.58    v1_xboole_0(k1_xboole_0) | ~spl5_5),
% 1.44/0.58    inference(avatar_component_clause,[],[f106])).
% 1.44/0.58  fof(f133,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | r1_xboole_0(X0,X1)) )),
% 1.44/0.58    inference(resolution,[],[f53,f48])).
% 1.44/0.58  fof(f48,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f1])).
% 1.44/0.58  fof(f1,axiom,(
% 1.44/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.58  fof(f53,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f29])).
% 1.44/0.58  fof(f29,plain,(
% 1.44/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.44/0.58    inference(ennf_transformation,[],[f21])).
% 1.44/0.58  fof(f21,plain,(
% 1.44/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.58    inference(rectify,[],[f4])).
% 1.44/0.58  fof(f4,axiom,(
% 1.44/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.44/0.58  fof(f56,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f7])).
% 1.44/0.58  fof(f7,axiom,(
% 1.44/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.44/0.58  fof(f869,plain,(
% 1.44/0.58    ~spl5_31 | spl5_41 | ~spl5_30),
% 1.44/0.58    inference(avatar_split_clause,[],[f868,f334,f444,f340])).
% 1.44/0.58  fof(f340,plain,(
% 1.44/0.58    spl5_31 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.44/0.58  fof(f444,plain,(
% 1.44/0.58    spl5_41 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.44/0.58  fof(f334,plain,(
% 1.44/0.58    spl5_30 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.44/0.58  fof(f868,plain,(
% 1.44/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_30),
% 1.44/0.58    inference(resolution,[],[f336,f243])).
% 1.44/0.58  fof(f243,plain,(
% 1.44/0.58    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.44/0.58    inference(forward_demodulation,[],[f81,f80])).
% 1.44/0.58  fof(f80,plain,(
% 1.44/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.44/0.58    inference(equality_resolution,[],[f62])).
% 1.44/0.58  fof(f62,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f8])).
% 1.44/0.58  fof(f8,axiom,(
% 1.44/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.44/0.58  fof(f81,plain,(
% 1.44/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.44/0.58    inference(equality_resolution,[],[f72])).
% 1.44/0.58  fof(f72,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f36])).
% 1.44/0.58  fof(f36,plain,(
% 1.44/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(flattening,[],[f35])).
% 1.44/0.58  fof(f35,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f15])).
% 1.44/0.58  fof(f15,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.44/0.58  fof(f336,plain,(
% 1.44/0.58    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl5_30),
% 1.44/0.58    inference(avatar_component_clause,[],[f334])).
% 1.44/0.58  fof(f825,plain,(
% 1.44/0.58    ~spl5_9 | ~spl5_1),
% 1.44/0.58    inference(avatar_split_clause,[],[f822,f87,f147])).
% 1.44/0.58  fof(f147,plain,(
% 1.44/0.58    spl5_9 <=> v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.44/0.58  fof(f87,plain,(
% 1.44/0.58    spl5_1 <=> r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.44/0.58  fof(f822,plain,(
% 1.44/0.58    ~v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) | ~spl5_1),
% 1.44/0.58    inference(resolution,[],[f89,f48])).
% 1.44/0.58  fof(f89,plain,(
% 1.44/0.58    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) | ~spl5_1),
% 1.44/0.58    inference(avatar_component_clause,[],[f87])).
% 1.44/0.58  fof(f824,plain,(
% 1.44/0.58    spl5_10 | ~spl5_1),
% 1.44/0.58    inference(avatar_split_clause,[],[f820,f87,f198])).
% 1.44/0.58  fof(f198,plain,(
% 1.44/0.58    spl5_10 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.44/0.58  fof(f820,plain,(
% 1.44/0.58    v1_funct_2(sK2,sK0,sK1) | ~spl5_1),
% 1.44/0.58    inference(resolution,[],[f89,f78])).
% 1.44/0.58  fof(f78,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f66,f50])).
% 1.44/0.58  fof(f50,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f18])).
% 1.44/0.58  fof(f18,axiom,(
% 1.44/0.58    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).
% 1.44/0.58  fof(f66,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_2(X2,X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f33])).
% 1.44/0.58  fof(f33,plain,(
% 1.44/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.44/0.58    inference(ennf_transformation,[],[f22])).
% 1.44/0.58  fof(f22,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 1.44/0.58    inference(pure_predicate_removal,[],[f17])).
% 1.44/0.58  fof(f17,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 1.44/0.58  fof(f823,plain,(
% 1.44/0.58    spl5_13 | ~spl5_1),
% 1.44/0.58    inference(avatar_split_clause,[],[f819,f87,f227])).
% 1.44/0.58  fof(f227,plain,(
% 1.44/0.58    spl5_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.44/0.58  fof(f819,plain,(
% 1.44/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_1),
% 1.44/0.58    inference(resolution,[],[f89,f77])).
% 1.44/0.58  fof(f77,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.58    inference(definition_unfolding,[],[f67,f50])).
% 1.44/0.58  fof(f67,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f33])).
% 1.44/0.58  fof(f813,plain,(
% 1.44/0.58    spl5_31 | ~spl5_33),
% 1.44/0.58    inference(avatar_split_clause,[],[f807,f351,f340])).
% 1.44/0.58  fof(f351,plain,(
% 1.44/0.58    spl5_33 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.44/0.58  fof(f807,plain,(
% 1.44/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_33),
% 1.44/0.58    inference(resolution,[],[f353,f57])).
% 1.44/0.58  fof(f57,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f9])).
% 1.44/0.58  fof(f9,axiom,(
% 1.44/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.58  fof(f353,plain,(
% 1.44/0.58    r1_tarski(sK2,k1_xboole_0) | ~spl5_33),
% 1.44/0.58    inference(avatar_component_clause,[],[f351])).
% 1.44/0.58  fof(f812,plain,(
% 1.44/0.58    spl5_39 | ~spl5_33),
% 1.44/0.58    inference(avatar_split_clause,[],[f806,f351,f413])).
% 1.44/0.58  fof(f806,plain,(
% 1.44/0.58    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) | ~spl5_33),
% 1.44/0.58    inference(resolution,[],[f353,f59])).
% 1.44/0.58  fof(f59,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f5])).
% 1.44/0.58  fof(f5,axiom,(
% 1.44/0.58    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.44/0.58  fof(f796,plain,(
% 1.44/0.58    spl5_33 | ~spl5_15 | ~spl5_26),
% 1.44/0.58    inference(avatar_split_clause,[],[f349,f305,f239,f351])).
% 1.44/0.58  fof(f239,plain,(
% 1.44/0.58    spl5_15 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.44/0.58  fof(f305,plain,(
% 1.44/0.58    spl5_26 <=> k1_xboole_0 = sK0),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.44/0.58  fof(f349,plain,(
% 1.44/0.58    r1_tarski(sK2,k1_xboole_0) | (~spl5_15 | ~spl5_26)),
% 1.44/0.58    inference(forward_demodulation,[],[f321,f80])).
% 1.44/0.58  fof(f321,plain,(
% 1.44/0.58    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl5_15 | ~spl5_26)),
% 1.44/0.58    inference(backward_demodulation,[],[f241,f307])).
% 1.44/0.58  fof(f307,plain,(
% 1.44/0.58    k1_xboole_0 = sK0 | ~spl5_26),
% 1.44/0.58    inference(avatar_component_clause,[],[f305])).
% 1.44/0.58  fof(f241,plain,(
% 1.44/0.58    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl5_15),
% 1.44/0.58    inference(avatar_component_clause,[],[f239])).
% 1.44/0.58  fof(f716,plain,(
% 1.44/0.58    k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK2) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK2)),
% 1.44/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.44/0.58  fof(f714,plain,(
% 1.44/0.58    spl5_26 | ~spl5_59),
% 1.44/0.58    inference(avatar_split_clause,[],[f713,f706,f305])).
% 1.44/0.58  fof(f706,plain,(
% 1.44/0.58    spl5_59 <=> v1_xboole_0(sK0)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 1.44/0.58  fof(f713,plain,(
% 1.44/0.58    k1_xboole_0 = sK0 | ~spl5_59),
% 1.44/0.58    inference(resolution,[],[f708,f46])).
% 1.44/0.58  fof(f46,plain,(
% 1.44/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f28])).
% 1.44/0.58  fof(f28,plain,(
% 1.44/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.44/0.58    inference(ennf_transformation,[],[f3])).
% 1.44/0.58  fof(f3,axiom,(
% 1.44/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.44/0.58  fof(f708,plain,(
% 1.44/0.58    v1_xboole_0(sK0) | ~spl5_59),
% 1.44/0.58    inference(avatar_component_clause,[],[f706])).
% 1.44/0.58  fof(f709,plain,(
% 1.44/0.58    spl5_59 | ~spl5_5 | spl5_42),
% 1.44/0.58    inference(avatar_split_clause,[],[f704,f465,f106,f706])).
% 1.44/0.58  fof(f465,plain,(
% 1.44/0.58    spl5_42 <=> v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.44/0.58  fof(f704,plain,(
% 1.44/0.58    v1_xboole_0(sK0) | (~spl5_5 | spl5_42)),
% 1.44/0.58    inference(resolution,[],[f467,f184])).
% 1.44/0.58  fof(f184,plain,(
% 1.44/0.58    ( ! [X0] : (v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl5_5),
% 1.44/0.58    inference(resolution,[],[f76,f108])).
% 1.44/0.58  fof(f76,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 1.44/0.58    inference(definition_unfolding,[],[f54,f50])).
% 1.44/0.58  fof(f54,plain,(
% 1.44/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f31])).
% 1.44/0.58  fof(f31,plain,(
% 1.44/0.58    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.44/0.58    inference(flattening,[],[f30])).
% 1.44/0.58  fof(f30,plain,(
% 1.44/0.58    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.44/0.58    inference(ennf_transformation,[],[f16])).
% 1.44/0.58  fof(f16,axiom,(
% 1.44/0.58    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 1.44/0.59  fof(f467,plain,(
% 1.44/0.59    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) | spl5_42),
% 1.44/0.59    inference(avatar_component_clause,[],[f465])).
% 1.44/0.59  fof(f689,plain,(
% 1.44/0.59    ~spl5_42 | spl5_9 | ~spl5_27),
% 1.44/0.59    inference(avatar_split_clause,[],[f688,f309,f147,f465])).
% 1.44/0.59  fof(f309,plain,(
% 1.44/0.59    spl5_27 <=> k1_xboole_0 = sK1),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.44/0.59  fof(f688,plain,(
% 1.44/0.59    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) | (spl5_9 | ~spl5_27)),
% 1.44/0.59    inference(forward_demodulation,[],[f149,f311])).
% 1.44/0.59  fof(f311,plain,(
% 1.44/0.59    k1_xboole_0 = sK1 | ~spl5_27),
% 1.44/0.59    inference(avatar_component_clause,[],[f309])).
% 1.44/0.59  fof(f149,plain,(
% 1.44/0.59    ~v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) | spl5_9),
% 1.44/0.59    inference(avatar_component_clause,[],[f147])).
% 1.44/0.59  fof(f666,plain,(
% 1.44/0.59    ~spl5_7 | spl5_57),
% 1.44/0.59    inference(avatar_contradiction_clause,[],[f664])).
% 1.44/0.59  fof(f664,plain,(
% 1.44/0.59    $false | (~spl5_7 | spl5_57)),
% 1.44/0.59    inference(resolution,[],[f661,f315])).
% 1.44/0.59  fof(f315,plain,(
% 1.44/0.59    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl5_7),
% 1.44/0.59    inference(trivial_inequality_removal,[],[f314])).
% 1.44/0.59  fof(f314,plain,(
% 1.44/0.59    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl5_7),
% 1.44/0.59    inference(forward_demodulation,[],[f313,f192])).
% 1.44/0.59  fof(f192,plain,(
% 1.44/0.59    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl5_7),
% 1.44/0.59    inference(forward_demodulation,[],[f189,f118])).
% 1.44/0.59  fof(f118,plain,(
% 1.44/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_7),
% 1.44/0.59    inference(avatar_component_clause,[],[f116])).
% 1.44/0.59  fof(f116,plain,(
% 1.44/0.59    spl5_7 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.44/0.59  fof(f189,plain,(
% 1.44/0.59    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.44/0.59    inference(resolution,[],[f68,f129])).
% 1.44/0.59  fof(f129,plain,(
% 1.44/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(resolution,[],[f57,f43])).
% 1.44/0.59  % (21702)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.59  fof(f68,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f34])).
% 1.44/0.59  fof(f34,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.59    inference(ennf_transformation,[],[f14])).
% 1.44/0.59  fof(f14,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.44/0.59  fof(f313,plain,(
% 1.44/0.59    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.44/0.59    inference(resolution,[],[f270,f129])).
% 1.44/0.59  fof(f270,plain,(
% 1.44/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.44/0.59    inference(forward_demodulation,[],[f82,f80])).
% 1.44/0.59  fof(f82,plain,(
% 1.44/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.44/0.59    inference(equality_resolution,[],[f71])).
% 1.44/0.59  fof(f71,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f36])).
% 1.44/0.59  fof(f661,plain,(
% 1.44/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl5_57),
% 1.44/0.59    inference(avatar_component_clause,[],[f659])).
% 1.44/0.59  fof(f659,plain,(
% 1.44/0.59    spl5_57 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 1.44/0.59  fof(f662,plain,(
% 1.44/0.59    ~spl5_57 | spl5_50 | ~spl5_51),
% 1.44/0.59    inference(avatar_split_clause,[],[f657,f596,f578,f659])).
% 1.44/0.59  fof(f578,plain,(
% 1.44/0.59    spl5_50 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.44/0.59  fof(f657,plain,(
% 1.44/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_50 | ~spl5_51)),
% 1.44/0.59    inference(forward_demodulation,[],[f580,f598])).
% 1.44/0.59  fof(f580,plain,(
% 1.44/0.59    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | spl5_50),
% 1.44/0.59    inference(avatar_component_clause,[],[f578])).
% 1.44/0.59  fof(f581,plain,(
% 1.44/0.59    ~spl5_50 | ~spl5_27 | spl5_30),
% 1.44/0.59    inference(avatar_split_clause,[],[f576,f334,f309,f578])).
% 1.44/0.59  fof(f576,plain,(
% 1.44/0.59    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_27 | spl5_30)),
% 1.44/0.59    inference(forward_demodulation,[],[f335,f311])).
% 1.44/0.59  fof(f335,plain,(
% 1.44/0.59    ~v1_funct_2(sK2,k1_xboole_0,sK1) | spl5_30),
% 1.44/0.59    inference(avatar_component_clause,[],[f334])).
% 1.44/0.59  fof(f535,plain,(
% 1.44/0.59    spl5_33 | ~spl5_15 | ~spl5_27),
% 1.44/0.59    inference(avatar_split_clause,[],[f534,f309,f239,f351])).
% 1.44/0.59  fof(f534,plain,(
% 1.44/0.59    r1_tarski(sK2,k1_xboole_0) | (~spl5_15 | ~spl5_27)),
% 1.44/0.59    inference(forward_demodulation,[],[f522,f79])).
% 1.44/0.59  fof(f79,plain,(
% 1.44/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.44/0.59    inference(equality_resolution,[],[f63])).
% 1.44/0.59  fof(f63,plain,(
% 1.44/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f8])).
% 1.44/0.59  fof(f522,plain,(
% 1.44/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl5_15 | ~spl5_27)),
% 1.44/0.59    inference(backward_demodulation,[],[f241,f311])).
% 1.44/0.59  fof(f509,plain,(
% 1.44/0.59    ~spl5_10 | spl5_27 | spl5_4 | ~spl5_13 | ~spl5_14),
% 1.44/0.59    inference(avatar_split_clause,[],[f508,f234,f227,f101,f309,f198])).
% 1.44/0.59  fof(f101,plain,(
% 1.44/0.59    spl5_4 <=> sK0 = k1_relat_1(sK2)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.44/0.59  fof(f234,plain,(
% 1.44/0.59    spl5_14 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.44/0.59  fof(f508,plain,(
% 1.44/0.59    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | (~spl5_13 | ~spl5_14)),
% 1.44/0.59    inference(forward_demodulation,[],[f504,f236])).
% 1.44/0.59  fof(f236,plain,(
% 1.44/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_14),
% 1.44/0.59    inference(avatar_component_clause,[],[f234])).
% 1.44/0.59  fof(f504,plain,(
% 1.44/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl5_13),
% 1.44/0.59    inference(resolution,[],[f74,f229])).
% 1.44/0.59  fof(f229,plain,(
% 1.44/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_13),
% 1.44/0.59    inference(avatar_component_clause,[],[f227])).
% 1.44/0.59  fof(f74,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f36])).
% 1.44/0.59  fof(f480,plain,(
% 1.44/0.59    spl5_14 | ~spl5_13),
% 1.44/0.59    inference(avatar_split_clause,[],[f478,f227,f234])).
% 1.44/0.59  fof(f478,plain,(
% 1.44/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_13),
% 1.44/0.59    inference(resolution,[],[f229,f68])).
% 1.44/0.59  fof(f474,plain,(
% 1.44/0.59    spl5_16 | ~spl5_2 | ~spl5_17 | ~spl5_15),
% 1.44/0.59    inference(avatar_split_clause,[],[f470,f239,f253,f92,f249])).
% 1.44/0.59  fof(f249,plain,(
% 1.44/0.59    spl5_16 <=> r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.44/0.59  fof(f92,plain,(
% 1.44/0.59    spl5_2 <=> v1_relat_1(sK2)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.44/0.59  fof(f253,plain,(
% 1.44/0.59    spl5_17 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.44/0.59  fof(f470,plain,(
% 1.44/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_15),
% 1.44/0.59    inference(resolution,[],[f241,f45])).
% 1.44/0.59  fof(f45,plain,(
% 1.44/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 1.44/0.59    inference(cnf_transformation,[],[f27])).
% 1.44/0.59  fof(f27,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.59    inference(flattening,[],[f26])).
% 1.44/0.59  fof(f26,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.59    inference(ennf_transformation,[],[f12])).
% 1.44/0.59  fof(f12,axiom,(
% 1.44/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.44/0.59  fof(f312,plain,(
% 1.44/0.59    spl5_26 | spl5_27 | spl5_3 | ~spl5_16),
% 1.44/0.59    inference(avatar_split_clause,[],[f275,f249,f97,f309,f305])).
% 1.44/0.59  fof(f275,plain,(
% 1.44/0.59    r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_16),
% 1.44/0.59    inference(superposition,[],[f251,f65])).
% 1.44/0.59  fof(f65,plain,(
% 1.44/0.59    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.59    inference(cnf_transformation,[],[f32])).
% 1.44/0.59  fof(f32,plain,(
% 1.44/0.59    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.44/0.59    inference(ennf_transformation,[],[f11])).
% 1.44/0.59  fof(f11,axiom,(
% 1.44/0.59    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.44/0.59  fof(f251,plain,(
% 1.44/0.59    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_16),
% 1.44/0.59    inference(avatar_component_clause,[],[f249])).
% 1.44/0.59  fof(f268,plain,(
% 1.44/0.59    spl5_17),
% 1.44/0.59    inference(avatar_contradiction_clause,[],[f267])).
% 1.44/0.59  fof(f267,plain,(
% 1.44/0.59    $false | spl5_17),
% 1.44/0.59    inference(resolution,[],[f255,f49])).
% 1.44/0.59  fof(f49,plain,(
% 1.44/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.44/0.59    inference(cnf_transformation,[],[f10])).
% 1.44/0.59  fof(f10,axiom,(
% 1.44/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.44/0.59  fof(f255,plain,(
% 1.44/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_17),
% 1.44/0.59    inference(avatar_component_clause,[],[f253])).
% 1.44/0.59  fof(f242,plain,(
% 1.44/0.59    spl5_15 | ~spl5_13),
% 1.44/0.59    inference(avatar_split_clause,[],[f232,f227,f239])).
% 1.44/0.59  fof(f232,plain,(
% 1.44/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl5_13),
% 1.44/0.59    inference(resolution,[],[f229,f58])).
% 1.44/0.59  fof(f58,plain,(
% 1.44/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f9])).
% 1.44/0.59  fof(f119,plain,(
% 1.44/0.59    spl5_7),
% 1.44/0.59    inference(avatar_split_clause,[],[f41,f116])).
% 1.44/0.59  fof(f41,plain,(
% 1.44/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.59    inference(cnf_transformation,[],[f13])).
% 1.44/0.59  fof(f13,axiom,(
% 1.44/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.44/0.59  fof(f114,plain,(
% 1.44/0.59    spl5_6),
% 1.44/0.59    inference(avatar_split_clause,[],[f42,f111])).
% 1.44/0.59  fof(f42,plain,(
% 1.44/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.44/0.59    inference(cnf_transformation,[],[f13])).
% 1.44/0.59  fof(f109,plain,(
% 1.44/0.59    spl5_5),
% 1.44/0.59    inference(avatar_split_clause,[],[f40,f106])).
% 1.44/0.59  fof(f40,plain,(
% 1.44/0.59    v1_xboole_0(k1_xboole_0)),
% 1.44/0.59    inference(cnf_transformation,[],[f2])).
% 1.44/0.59  fof(f2,axiom,(
% 1.44/0.59    v1_xboole_0(k1_xboole_0)),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.44/0.59  fof(f104,plain,(
% 1.44/0.59    ~spl5_3 | ~spl5_4),
% 1.44/0.59    inference(avatar_split_clause,[],[f37,f101,f97])).
% 1.44/0.59  fof(f37,plain,(
% 1.44/0.59    sK0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.44/0.59    inference(cnf_transformation,[],[f25])).
% 1.44/0.59  fof(f25,plain,(
% 1.44/0.59    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 1.44/0.59    inference(flattening,[],[f24])).
% 1.44/0.59  fof(f24,plain,(
% 1.44/0.59    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 1.44/0.59    inference(ennf_transformation,[],[f23])).
% 1.44/0.59  fof(f23,plain,(
% 1.44/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.44/0.59    inference(pure_predicate_removal,[],[f20])).
% 1.44/0.59  fof(f20,negated_conjecture,(
% 1.44/0.59    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.44/0.59    inference(negated_conjecture,[],[f19])).
% 1.44/0.59  fof(f19,conjecture,(
% 1.44/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 1.44/0.59  fof(f95,plain,(
% 1.44/0.59    spl5_2),
% 1.44/0.59    inference(avatar_split_clause,[],[f38,f92])).
% 1.44/0.59  fof(f38,plain,(
% 1.44/0.59    v1_relat_1(sK2)),
% 1.44/0.59    inference(cnf_transformation,[],[f25])).
% 1.44/0.59  fof(f90,plain,(
% 1.44/0.59    spl5_1),
% 1.44/0.59    inference(avatar_split_clause,[],[f75,f87])).
% 1.44/0.59  fof(f75,plain,(
% 1.44/0.59    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 1.44/0.59    inference(definition_unfolding,[],[f39,f50])).
% 1.44/0.59  fof(f39,plain,(
% 1.44/0.59    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.44/0.59    inference(cnf_transformation,[],[f25])).
% 1.44/0.59  % SZS output end Proof for theBenchmark
% 1.44/0.59  % (21715)------------------------------
% 1.44/0.59  % (21715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (21715)Termination reason: Refutation
% 1.44/0.59  
% 1.44/0.59  % (21715)Memory used [KB]: 11257
% 1.44/0.59  % (21715)Time elapsed: 0.160 s
% 1.44/0.59  % (21715)------------------------------
% 1.44/0.59  % (21715)------------------------------
% 1.44/0.59  % (21690)Success in time 0.226 s
%------------------------------------------------------------------------------
