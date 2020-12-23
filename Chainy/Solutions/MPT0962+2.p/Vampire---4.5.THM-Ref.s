%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0962+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 168 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 ( 631 expanded)
%              Number of equality atoms :   70 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4015,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2136,f2137,f2247,f2387,f2644,f3237,f3240,f3872,f3875,f3877,f3996])).

fof(f3996,plain,(
    spl37_3 ),
    inference(avatar_contradiction_clause,[],[f3995])).

fof(f3995,plain,
    ( $false
    | spl37_3 ),
    inference(subsumption_resolution,[],[f3994,f1772])).

fof(f1772,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1667])).

fof(f1667,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1483,f1666])).

fof(f1666,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1483,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1482])).

fof(f1482,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1479])).

fof(f1479,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1478])).

fof(f1478,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f3994,plain,
    ( ~ v1_relat_1(sK1)
    | spl37_3 ),
    inference(subsumption_resolution,[],[f3993,f2101])).

fof(f2101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1865])).

fof(f1865,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f1704,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1703])).

fof(f1703,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3993,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl37_3 ),
    inference(subsumption_resolution,[],[f3980,f1774])).

fof(f1774,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f1667])).

fof(f3980,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl37_3 ),
    inference(resolution,[],[f2135,f1870])).

fof(f1870,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1542])).

fof(f1542,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1541])).

fof(f1541,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1240])).

fof(f1240,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f2135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl37_3 ),
    inference(avatar_component_clause,[],[f2133])).

fof(f2133,plain,
    ( spl37_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3])])).

fof(f3877,plain,
    ( ~ spl37_3
    | spl37_38
    | spl37_2 ),
    inference(avatar_split_clause,[],[f2971,f2129,f2808,f2133])).

fof(f2808,plain,
    ( spl37_38
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_38])])).

fof(f2129,plain,
    ( spl37_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2])])).

fof(f2971,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl37_2 ),
    inference(subsumption_resolution,[],[f2395,f1988])).

fof(f1988,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1605])).

fof(f1605,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2395,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl37_2 ),
    inference(resolution,[],[f2131,f1839])).

fof(f1839,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1693])).

fof(f1693,plain,(
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
    inference(nnf_transformation,[],[f1527])).

fof(f1527,plain,(
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
    inference(flattening,[],[f1526])).

fof(f1526,plain,(
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
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
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

fof(f2131,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl37_2 ),
    inference(avatar_component_clause,[],[f2129])).

fof(f3875,plain,
    ( spl37_10
    | ~ spl37_26
    | ~ spl37_38 ),
    inference(avatar_contradiction_clause,[],[f3874])).

fof(f3874,plain,
    ( $false
    | spl37_10
    | ~ spl37_26
    | ~ spl37_38 ),
    inference(subsumption_resolution,[],[f3873,f2234])).

fof(f2234,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl37_10 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f2232,plain,
    ( spl37_10
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_10])])).

fof(f3873,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl37_26
    | ~ spl37_38 ),
    inference(forward_demodulation,[],[f2385,f2810])).

fof(f2810,plain,
    ( k1_xboole_0 = sK0
    | ~ spl37_38 ),
    inference(avatar_component_clause,[],[f2808])).

fof(f2385,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl37_26 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f2383,plain,
    ( spl37_26
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_26])])).

fof(f3872,plain,
    ( spl37_25
    | ~ spl37_38 ),
    inference(avatar_contradiction_clause,[],[f3871])).

fof(f3871,plain,
    ( $false
    | spl37_25
    | ~ spl37_38 ),
    inference(subsumption_resolution,[],[f3820,f1916])).

fof(f1916,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3820,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl37_25
    | ~ spl37_38 ),
    inference(superposition,[],[f2381,f2810])).

fof(f2381,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl37_25 ),
    inference(avatar_component_clause,[],[f2379])).

fof(f2379,plain,
    ( spl37_25
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_25])])).

fof(f3240,plain,
    ( ~ spl37_28
    | spl37_2
    | ~ spl37_12
    | ~ spl37_38 ),
    inference(avatar_split_clause,[],[f3239,f2808,f2243,f2129,f2641])).

fof(f2641,plain,
    ( spl37_28
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_28])])).

fof(f2243,plain,
    ( spl37_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_12])])).

fof(f3239,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl37_2
    | ~ spl37_12
    | ~ spl37_38 ),
    inference(forward_demodulation,[],[f3238,f1900])).

fof(f1900,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f3238,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl37_2
    | ~ spl37_12
    | ~ spl37_38 ),
    inference(forward_demodulation,[],[f3231,f2810])).

fof(f3231,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK0)
    | spl37_2
    | ~ spl37_12 ),
    inference(superposition,[],[f2131,f2245])).

fof(f2245,plain,
    ( k1_xboole_0 = sK1
    | ~ spl37_12 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f3237,plain,
    ( ~ spl37_1
    | ~ spl37_12
    | spl37_27 ),
    inference(avatar_contradiction_clause,[],[f3236])).

fof(f3236,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_12
    | spl37_27 ),
    inference(subsumption_resolution,[],[f3230,f2639])).

fof(f2639,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl37_27 ),
    inference(avatar_component_clause,[],[f2637])).

fof(f2637,plain,
    ( spl37_27
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_27])])).

fof(f3230,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl37_1
    | ~ spl37_12 ),
    inference(superposition,[],[f2126,f2245])).

fof(f2126,plain,
    ( v1_funct_1(sK1)
    | ~ spl37_1 ),
    inference(avatar_component_clause,[],[f2125])).

fof(f2125,plain,
    ( spl37_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_1])])).

fof(f2644,plain,
    ( ~ spl37_27
    | spl37_28 ),
    inference(avatar_split_clause,[],[f2635,f2641,f2637])).

fof(f2635,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f2634,f1900])).

fof(f2634,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f2506,f1901])).

fof(f1901,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f2506,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f2496,f1850])).

fof(f1850,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1529])).

fof(f1529,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1528])).

fof(f1528,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1477])).

fof(f1477,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f2496,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f2200,f2090])).

fof(f2090,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f2200,plain,(
    ! [X83] : v1_relat_1(k3_xboole_0(sK1,X83)) ),
    inference(resolution,[],[f1772,f2082])).

fof(f2082,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1664])).

fof(f1664,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f689])).

fof(f689,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f2387,plain,
    ( ~ spl37_25
    | spl37_26 ),
    inference(avatar_split_clause,[],[f2302,f2383,f2379])).

fof(f2302,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f1774,f1867])).

fof(f1867,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f2247,plain,
    ( ~ spl37_10
    | spl37_12 ),
    inference(avatar_split_clause,[],[f2161,f2243,f2232])).

fof(f2161,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k2_relat_1(sK1) ),
    inference(resolution,[],[f1772,f1897])).

fof(f1897,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1561])).

fof(f1561,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1560])).

fof(f1560,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f859])).

fof(f859,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f2137,plain,(
    spl37_1 ),
    inference(avatar_split_clause,[],[f1773,f2125])).

fof(f1773,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1667])).

fof(f2136,plain,
    ( ~ spl37_1
    | ~ spl37_2
    | ~ spl37_3 ),
    inference(avatar_split_clause,[],[f1775,f2133,f2129,f2125])).

fof(f1775,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1667])).
%------------------------------------------------------------------------------
