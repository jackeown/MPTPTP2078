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
% DateTime   : Thu Dec  3 13:05:50 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  299 ( 671 expanded)
%              Number of leaves         :   75 ( 324 expanded)
%              Depth                    :   10
%              Number of atoms          :  992 (2028 expanded)
%              Number of equality atoms :  133 ( 243 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2783,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f206,f225,f337,f355,f362,f439,f444,f449,f454,f459,f733,f766,f835,f854,f859,f884,f1244,f1249,f1386,f1391,f1433,f1446,f1540,f1541,f1734,f1738,f1806,f1818,f1830,f1849,f2061,f2081,f2130,f2131,f2192,f2217,f2395,f2694,f2721,f2763,f2764,f2766,f2774,f2782])).

fof(f2782,plain,
    ( k5_relat_1(sK6,k2_funct_1(sK6)) != k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_1(sK6))
    | k2_funct_2(sK5,sK6) != k2_funct_1(sK6)
    | r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5))
    | ~ r2_relset_1(sK5,sK5,k5_relat_1(sK6,k2_funct_1(sK6)),k6_partfun1(sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2774,plain,
    ( spl10_81
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(avatar_split_clause,[],[f1831,f1647,f1642,f896])).

fof(f896,plain,
    ( spl10_81
  <=> v1_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f1642,plain,
    ( spl10_166
  <=> sP0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f1647,plain,
    ( spl10_167
  <=> k2_funct_2(sK5,sK6) = k2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_167])])).

fof(f1831,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(forward_demodulation,[],[f1786,f1649])).

fof(f1649,plain,
    ( k2_funct_2(sK5,sK6) = k2_funct_1(sK6)
    | ~ spl10_167 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f1786,plain,
    ( v1_funct_1(k2_funct_2(sK5,sK6))
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f1644,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1644,plain,
    ( sP0(sK5,sK6)
    | ~ spl10_166 ),
    inference(avatar_component_clause,[],[f1642])).

fof(f2766,plain,
    ( k6_partfun1(sK5) != k5_relat_1(sK6,k2_funct_1(sK6))
    | r2_relset_1(sK5,sK5,k5_relat_1(sK6,k2_funct_1(sK6)),k6_partfun1(sK5))
    | ~ r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2764,plain,
    ( k5_relat_1(k2_funct_1(sK6),sK6) != k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_1(sK6),sK6)
    | k2_funct_2(sK5,sK6) != k2_funct_1(sK6)
    | r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5))
    | ~ r2_relset_1(sK5,sK5,k5_relat_1(k2_funct_1(sK6),sK6),k6_partfun1(sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2763,plain,(
    spl10_255 ),
    inference(avatar_contradiction_clause,[],[f2762])).

fof(f2762,plain,
    ( $false
    | spl10_255 ),
    inference(trivial_inequality_removal,[],[f2760])).

fof(f2760,plain,
    ( k11_relat_1(k6_partfun1(sK5),sK8(sK5,k6_partfun1(sK5),k6_partfun1(sK5))) != k11_relat_1(k6_partfun1(sK5),sK8(sK5,k6_partfun1(sK5),k6_partfun1(sK5)))
    | spl10_255 ),
    inference(unit_resulting_resolution,[],[f77,f77,f2439,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k11_relat_1(X1,sK8(X0,X1,X2)) != k11_relat_1(X2,sK8(X0,X1,X2))
      | r2_relset_1(X0,X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK8(X0,X1,X2)) != k11_relat_1(X2,sK8(X0,X1,X2))
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f27,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK8(X0,X1,X2)) != k11_relat_1(X2,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(f2439,plain,
    ( ~ r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5))
    | spl10_255 ),
    inference(avatar_component_clause,[],[f2438])).

fof(f2438,plain,
    ( spl10_255
  <=> r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_255])])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f2721,plain,
    ( ~ spl10_255
    | spl10_199
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f2706,f2691,f1911,f2438])).

fof(f1911,plain,
    ( spl10_199
  <=> r2_relset_1(sK5,sK5,k5_relat_1(k2_funct_1(sK6),sK6),k6_partfun1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_199])])).

fof(f2691,plain,
    ( spl10_292
  <=> k6_partfun1(sK5) = k5_relat_1(k2_funct_1(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_292])])).

fof(f2706,plain,
    ( ~ r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5))
    | spl10_199
    | ~ spl10_292 ),
    inference(backward_demodulation,[],[f1913,f2693])).

fof(f2693,plain,
    ( k6_partfun1(sK5) = k5_relat_1(k2_funct_1(sK6),sK6)
    | ~ spl10_292 ),
    inference(avatar_component_clause,[],[f2691])).

fof(f1913,plain,
    ( ~ r2_relset_1(sK5,sK5,k5_relat_1(k2_funct_1(sK6),sK6),k6_partfun1(sK5))
    | spl10_199 ),
    inference(avatar_component_clause,[],[f1911])).

fof(f2694,plain,
    ( spl10_292
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_25
    | spl10_31
    | ~ spl10_236 ),
    inference(avatar_split_clause,[],[f2675,f2214,f399,f345,f144,f139,f129,f2691])).

fof(f129,plain,
    ( spl10_3
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f139,plain,
    ( spl10_5
  <=> v1_funct_2(sK6,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f144,plain,
    ( spl10_6
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f345,plain,
    ( spl10_25
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f399,plain,
    ( spl10_31
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f2214,plain,
    ( spl10_236
  <=> sK5 = k2_relset_1(sK5,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).

fof(f2675,plain,
    ( k6_partfun1(sK5) = k5_relat_1(k2_funct_1(sK6),sK6)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_25
    | spl10_31
    | ~ spl10_236 ),
    inference(unit_resulting_resolution,[],[f146,f347,f400,f141,f131,f2216,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f2216,plain,
    ( sK5 = k2_relset_1(sK5,sK5,sK6)
    | ~ spl10_236 ),
    inference(avatar_component_clause,[],[f2214])).

fof(f131,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f141,plain,
    ( v1_funct_2(sK6,sK5,sK5)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f400,plain,
    ( k1_xboole_0 != sK5
    | spl10_31 ),
    inference(avatar_component_clause,[],[f399])).

fof(f347,plain,
    ( v2_funct_1(sK6)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f345])).

fof(f146,plain,
    ( v1_funct_1(sK6)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f2395,plain,
    ( spl10_248
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_25
    | spl10_31
    | ~ spl10_236 ),
    inference(avatar_split_clause,[],[f2387,f2214,f399,f345,f144,f139,f129,f2392])).

fof(f2392,plain,
    ( spl10_248
  <=> k6_partfun1(sK5) = k5_relat_1(sK6,k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).

fof(f2387,plain,
    ( k6_partfun1(sK5) = k5_relat_1(sK6,k2_funct_1(sK6))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_25
    | spl10_31
    | ~ spl10_236 ),
    inference(unit_resulting_resolution,[],[f146,f347,f400,f141,f131,f2216,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2217,plain,
    ( spl10_236
    | ~ spl10_21
    | ~ spl10_233 ),
    inference(avatar_split_clause,[],[f2207,f2189,f306,f2214])).

fof(f306,plain,
    ( spl10_21
  <=> k2_relset_1(sK5,sK5,sK6) = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f2189,plain,
    ( spl10_233
  <=> sK5 = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_233])])).

fof(f2207,plain,
    ( sK5 = k2_relset_1(sK5,sK5,sK6)
    | ~ spl10_21
    | ~ spl10_233 ),
    inference(backward_demodulation,[],[f308,f2191])).

fof(f2191,plain,
    ( sK5 = k2_relat_1(sK6)
    | ~ spl10_233 ),
    inference(avatar_component_clause,[],[f2189])).

fof(f308,plain,
    ( k2_relset_1(sK5,sK5,sK6) = k2_relat_1(sK6)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f306])).

fof(f2192,plain,
    ( spl10_233
    | ~ spl10_27
    | ~ spl10_225 ),
    inference(avatar_split_clause,[],[f2187,f2127,f359,f2189])).

fof(f359,plain,
    ( spl10_27
  <=> k2_relat_1(sK6) = k1_relat_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f2127,plain,
    ( spl10_225
  <=> sK5 = k1_relat_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_225])])).

fof(f2187,plain,
    ( sK5 = k2_relat_1(sK6)
    | ~ spl10_27
    | ~ spl10_225 ),
    inference(backward_demodulation,[],[f361,f2129])).

fof(f2129,plain,
    ( sK5 = k1_relat_1(k2_funct_1(sK6))
    | ~ spl10_225 ),
    inference(avatar_component_clause,[],[f2127])).

fof(f361,plain,
    ( k2_relat_1(sK6) = k1_relat_1(k2_funct_1(sK6))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f359])).

fof(f2131,plain,
    ( spl10_21
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f1607,f129,f306])).

fof(f1607,plain,
    ( k2_relset_1(sK5,sK5,sK6) = k2_relat_1(sK6)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f131,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2130,plain,
    ( spl10_225
    | ~ spl10_193
    | ~ spl10_197 ),
    inference(avatar_split_clause,[],[f2099,f1846,f1815,f2127])).

fof(f1815,plain,
    ( spl10_193
  <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_193])])).

fof(f1846,plain,
    ( spl10_197
  <=> sK5 = k1_relset_1(sK5,sK5,k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_197])])).

fof(f2099,plain,
    ( sK5 = k1_relat_1(k2_funct_1(sK6))
    | ~ spl10_193
    | ~ spl10_197 ),
    inference(forward_demodulation,[],[f1935,f1848])).

fof(f1848,plain,
    ( sK5 = k1_relset_1(sK5,sK5,k2_funct_1(sK6))
    | ~ spl10_197 ),
    inference(avatar_component_clause,[],[f1846])).

fof(f1935,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k1_relset_1(sK5,sK5,k2_funct_1(sK6))
    | ~ spl10_193 ),
    inference(unit_resulting_resolution,[],[f1817,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1817,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ spl10_193 ),
    inference(avatar_component_clause,[],[f1815])).

fof(f2081,plain,
    ( spl10_220
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_81
    | ~ spl10_193 ),
    inference(avatar_split_clause,[],[f1943,f1815,f896,f144,f129,f2078])).

fof(f2078,plain,
    ( spl10_220
  <=> k5_relat_1(k2_funct_1(sK6),sK6) = k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_1(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_220])])).

fof(f1943,plain,
    ( k5_relat_1(k2_funct_1(sK6),sK6) = k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_1(sK6),sK6)
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_81
    | ~ spl10_193 ),
    inference(unit_resulting_resolution,[],[f146,f898,f131,f1817,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f898,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ spl10_81 ),
    inference(avatar_component_clause,[],[f896])).

fof(f2061,plain,
    ( spl10_216
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_81
    | ~ spl10_193 ),
    inference(avatar_split_clause,[],[f1947,f1815,f896,f144,f129,f2058])).

fof(f2058,plain,
    ( spl10_216
  <=> k5_relat_1(sK6,k2_funct_1(sK6)) = k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f1947,plain,
    ( k5_relat_1(sK6,k2_funct_1(sK6)) = k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_1(sK6))
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_81
    | ~ spl10_193 ),
    inference(unit_resulting_resolution,[],[f146,f131,f898,f1817,f110])).

fof(f1849,plain,
    ( spl10_197
    | spl10_31
    | ~ spl10_191
    | ~ spl10_195 ),
    inference(avatar_split_clause,[],[f1844,f1827,f1803,f399,f1846])).

fof(f1803,plain,
    ( spl10_191
  <=> sP2(sK5,k2_funct_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).

fof(f1827,plain,
    ( spl10_195
  <=> v1_funct_2(k2_funct_1(sK6),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_195])])).

fof(f1844,plain,
    ( sK5 = k1_relset_1(sK5,sK5,k2_funct_1(sK6))
    | spl10_31
    | ~ spl10_191
    | ~ spl10_195 ),
    inference(unit_resulting_resolution,[],[f1590,f1805,f1829,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1829,plain,
    ( v1_funct_2(k2_funct_1(sK6),sK5,sK5)
    | ~ spl10_195 ),
    inference(avatar_component_clause,[],[f1827])).

fof(f1805,plain,
    ( sP2(sK5,k2_funct_1(sK6),sK5)
    | ~ spl10_191 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f1590,plain,
    ( ! [X0] : ~ sP1(X0,sK5)
    | spl10_31 ),
    inference(unit_resulting_resolution,[],[f400,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1830,plain,
    ( spl10_195
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(avatar_split_clause,[],[f1825,f1647,f1642,f1827])).

fof(f1825,plain,
    ( v1_funct_2(k2_funct_1(sK6),sK5,sK5)
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(forward_demodulation,[],[f1787,f1649])).

fof(f1787,plain,
    ( v1_funct_2(k2_funct_2(sK5,sK6),sK5,sK5)
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f1644,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1818,plain,
    ( spl10_193
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(avatar_split_clause,[],[f1813,f1647,f1642,f1815])).

fof(f1813,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(forward_demodulation,[],[f1789,f1649])).

fof(f1789,plain,
    ( m1_subset_1(k2_funct_2(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f1644,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1806,plain,
    ( spl10_191
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(avatar_split_clause,[],[f1801,f1647,f1642,f1803])).

fof(f1801,plain,
    ( sP2(sK5,k2_funct_1(sK6),sK5)
    | ~ spl10_166
    | ~ spl10_167 ),
    inference(forward_demodulation,[],[f1791,f1649])).

fof(f1791,plain,
    ( sP2(sK5,k2_funct_2(sK5,sK6),sK5)
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f1644,f282])).

fof(f282,plain,(
    ! [X2,X3] :
      ( sP2(X2,k2_funct_2(X2,X3),X2)
      | ~ sP0(X2,X3) ) ),
    inference(resolution,[],[f89,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f36,f52,f51,f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1738,plain,
    ( spl10_166
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f1737,f144,f139,f134,f129,f1642])).

fof(f134,plain,
    ( spl10_4
  <=> v3_funct_2(sK6,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f1737,plain,
    ( sP0(sK5,sK6)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f1736,f146])).

fof(f1736,plain,
    ( sP0(sK5,sK6)
    | ~ v1_funct_1(sK6)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f1735,f141])).

fof(f1735,plain,
    ( sP0(sK5,sK6)
    | ~ v1_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_1(sK6)
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1637,f136])).

fof(f136,plain,
    ( v3_funct_2(sK6,sK5,sK5)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1637,plain,
    ( sP0(sK5,sK6)
    | ~ v3_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_1(sK6)
    | ~ spl10_3 ),
    inference(resolution,[],[f131,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f31,f48])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1734,plain,
    ( spl10_167
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f1733,f144,f139,f134,f129,f1647])).

fof(f1733,plain,
    ( k2_funct_2(sK5,sK6) = k2_funct_1(sK6)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f1732,f146])).

fof(f1732,plain,
    ( k2_funct_2(sK5,sK6) = k2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f1731,f141])).

fof(f1731,plain,
    ( k2_funct_2(sK5,sK6) = k2_funct_1(sK6)
    | ~ v1_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_1(sK6)
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1636,f136])).

fof(f1636,plain,
    ( k2_funct_2(sK5,sK6) = k2_funct_1(sK6)
    | ~ v3_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_1(sK6)
    | ~ spl10_3 ),
    inference(resolution,[],[f131,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f1541,plain,
    ( spl10_156
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81
    | ~ spl10_147 ),
    inference(avatar_split_clause,[],[f1487,f1383,f896,f881,f446,f144,f1443])).

fof(f1443,plain,
    ( spl10_156
  <=> m1_subset_1(k5_relat_1(k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).

fof(f446,plain,
    ( spl10_36
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f881,plain,
    ( spl10_78
  <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f1383,plain,
    ( spl10_147
  <=> k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6) = k5_relat_1(k2_funct_1(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_147])])).

fof(f1487,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81
    | ~ spl10_147 ),
    inference(forward_demodulation,[],[f1468,f1385])).

fof(f1385,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6) = k5_relat_1(k2_funct_1(sK6),sK6)
    | ~ spl10_147 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f1468,plain,
    ( m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81 ),
    inference(unit_resulting_resolution,[],[f146,f898,f883,f448,f112])).

fof(f112,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f448,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f446])).

fof(f883,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1540,plain,
    ( spl10_154
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81
    | ~ spl10_148 ),
    inference(avatar_split_clause,[],[f1490,f1388,f896,f881,f446,f144,f1430])).

fof(f1430,plain,
    ( spl10_154
  <=> m1_subset_1(k5_relat_1(sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f1388,plain,
    ( spl10_148
  <=> k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)) = k5_relat_1(sK6,k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).

fof(f1490,plain,
    ( m1_subset_1(k5_relat_1(sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81
    | ~ spl10_148 ),
    inference(forward_demodulation,[],[f1467,f1390])).

fof(f1390,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)) = k5_relat_1(sK6,k2_funct_1(sK6))
    | ~ spl10_148 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1467,plain,
    ( m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81 ),
    inference(unit_resulting_resolution,[],[f146,f448,f898,f883,f112])).

fof(f1446,plain,
    ( ~ spl10_156
    | spl10_122
    | ~ spl10_147 ),
    inference(avatar_split_clause,[],[f1435,f1383,f1241,f1443])).

fof(f1241,plain,
    ( spl10_122
  <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f1435,plain,
    ( ~ m1_subset_1(k5_relat_1(k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl10_122
    | ~ spl10_147 ),
    inference(backward_demodulation,[],[f1243,f1385])).

fof(f1243,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl10_122 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1433,plain,
    ( ~ spl10_154
    | spl10_123
    | ~ spl10_148 ),
    inference(avatar_split_clause,[],[f1422,f1388,f1246,f1430])).

fof(f1246,plain,
    ( spl10_123
  <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).

fof(f1422,plain,
    ( ~ m1_subset_1(k5_relat_1(sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl10_123
    | ~ spl10_148 ),
    inference(backward_demodulation,[],[f1248,f1390])).

fof(f1248,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl10_123 ),
    inference(avatar_component_clause,[],[f1246])).

fof(f1391,plain,
    ( spl10_148
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81 ),
    inference(avatar_split_clause,[],[f1370,f896,f881,f446,f144,f1388])).

fof(f1370,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)) = k5_relat_1(sK6,k2_funct_1(sK6))
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81 ),
    inference(unit_resulting_resolution,[],[f146,f448,f898,f883,f110])).

fof(f1386,plain,
    ( spl10_147
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81 ),
    inference(avatar_split_clause,[],[f1371,f896,f881,f446,f144,f1383])).

fof(f1371,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6) = k5_relat_1(k2_funct_1(sK6),sK6)
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_78
    | ~ spl10_81 ),
    inference(unit_resulting_resolution,[],[f146,f898,f883,f448,f110])).

fof(f1249,plain,
    ( ~ spl10_123
    | ~ spl10_15
    | spl10_72 ),
    inference(avatar_split_clause,[],[f1130,f851,f220,f1246])).

fof(f220,plain,
    ( spl10_15
  <=> sP9(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f851,plain,
    ( spl10_72
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f1130,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_15
    | spl10_72 ),
    inference(unit_resulting_resolution,[],[f853,f226,f77,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_relset_1(X0,X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f226,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f222,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f109,f117_D])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f117_D])).

fof(f117_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f222,plain,
    ( sP9(k1_xboole_0)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f220])).

fof(f853,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k6_partfun1(k1_xboole_0))
    | spl10_72 ),
    inference(avatar_component_clause,[],[f851])).

fof(f1244,plain,
    ( ~ spl10_122
    | ~ spl10_15
    | spl10_73 ),
    inference(avatar_split_clause,[],[f1131,f856,f220,f1241])).

fof(f856,plain,
    ( spl10_73
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f1131,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_15
    | spl10_73 ),
    inference(unit_resulting_resolution,[],[f858,f226,f77,f83])).

fof(f858,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k6_partfun1(k1_xboole_0))
    | spl10_73 ),
    inference(avatar_component_clause,[],[f856])).

fof(f884,plain,
    ( spl10_78
    | ~ spl10_63
    | ~ spl10_71 ),
    inference(avatar_split_clause,[],[f842,f825,f763,f881])).

fof(f763,plain,
    ( spl10_63
  <=> m1_subset_1(k2_funct_2(k1_xboole_0,sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f825,plain,
    ( spl10_71
  <=> k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f842,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_63
    | ~ spl10_71 ),
    inference(backward_demodulation,[],[f765,f827])).

fof(f827,plain,
    ( k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6)
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f825])).

fof(f765,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f763])).

fof(f859,plain,
    ( ~ spl10_73
    | spl10_35
    | ~ spl10_71 ),
    inference(avatar_split_clause,[],[f837,f825,f441,f856])).

fof(f441,plain,
    ( spl10_35
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,sK6),sK6),k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f837,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k6_partfun1(k1_xboole_0))
    | spl10_35
    | ~ spl10_71 ),
    inference(backward_demodulation,[],[f443,f827])).

fof(f443,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,sK6),sK6),k6_partfun1(k1_xboole_0))
    | spl10_35 ),
    inference(avatar_component_clause,[],[f441])).

fof(f854,plain,
    ( ~ spl10_72
    | spl10_34
    | ~ spl10_71 ),
    inference(avatar_split_clause,[],[f836,f825,f436,f851])).

fof(f436,plain,
    ( spl10_34
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_2(k1_xboole_0,sK6)),k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f836,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k6_partfun1(k1_xboole_0))
    | spl10_34
    | ~ spl10_71 ),
    inference(backward_demodulation,[],[f438,f827])).

fof(f438,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_2(k1_xboole_0,sK6)),k6_partfun1(k1_xboole_0))
    | spl10_34 ),
    inference(avatar_component_clause,[],[f436])).

fof(f835,plain,
    ( spl10_71
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f834,f456,f451,f446,f144,f825])).

fof(f451,plain,
    ( spl10_37
  <=> v3_funct_2(sK6,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f456,plain,
    ( spl10_38
  <=> v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f834,plain,
    ( k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6)
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f833,f146])).

fof(f833,plain,
    ( k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6)
    | ~ v1_funct_1(sK6)
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f832,f458])).

fof(f458,plain,
    ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f456])).

fof(f832,plain,
    ( k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6)
    | ~ v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_36
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f822,f453])).

fof(f453,plain,
    ( v3_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f451])).

fof(f822,plain,
    ( k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6)
    | ~ v3_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_36 ),
    inference(resolution,[],[f85,f448])).

fof(f766,plain,
    ( spl10_63
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f737,f723,f763])).

fof(f723,plain,
    ( spl10_58
  <=> sP0(k1_xboole_0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f737,plain,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_58 ),
    inference(unit_resulting_resolution,[],[f725,f89])).

fof(f725,plain,
    ( sP0(k1_xboole_0,sK6)
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f723])).

fof(f733,plain,
    ( spl10_58
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f732,f456,f451,f446,f144,f723])).

fof(f732,plain,
    ( sP0(k1_xboole_0,sK6)
    | ~ spl10_6
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f731,f146])).

fof(f731,plain,
    ( sP0(k1_xboole_0,sK6)
    | ~ v1_funct_1(sK6)
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f730,f458])).

fof(f730,plain,
    ( sP0(k1_xboole_0,sK6)
    | ~ v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_36
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f720,f453])).

fof(f720,plain,
    ( sP0(k1_xboole_0,sK6)
    | ~ v3_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_36 ),
    inference(resolution,[],[f90,f448])).

fof(f459,plain,
    ( spl10_38
    | ~ spl10_5
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f420,f399,f139,f456])).

fof(f420,plain,
    ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ spl10_5
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f141,f401])).

fof(f401,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f399])).

fof(f454,plain,
    ( spl10_37
    | ~ spl10_4
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f419,f399,f134,f451])).

fof(f419,plain,
    ( v3_funct_2(sK6,k1_xboole_0,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f136,f401])).

fof(f449,plain,
    ( spl10_36
    | ~ spl10_3
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f418,f399,f129,f446])).

fof(f418,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl10_3
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f131,f401])).

fof(f444,plain,
    ( ~ spl10_35
    | spl10_2
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f417,f399,f124,f441])).

fof(f124,plain,
    ( spl10_2
  <=> r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f417,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,sK6),sK6),k6_partfun1(k1_xboole_0))
    | spl10_2
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f126,f401])).

fof(f126,plain,
    ( ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f439,plain,
    ( ~ spl10_34
    | spl10_1
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f416,f399,f120,f436])).

fof(f120,plain,
    ( spl10_1
  <=> r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f416,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_2(k1_xboole_0,sK6)),k6_partfun1(k1_xboole_0))
    | spl10_1
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f122,f401])).

fof(f122,plain,
    ( ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f362,plain,
    ( spl10_27
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f357,f345,f196,f144,f359])).

fof(f196,plain,
    ( spl10_12
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f357,plain,
    ( k2_relat_1(sK6) = k1_relat_1(k2_funct_1(sK6))
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f198,f146,f347,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f198,plain,
    ( v1_relat_1(sK6)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f355,plain,
    ( spl10_25
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f342,f321,f345])).

fof(f321,plain,
    ( spl10_22
  <=> sP4(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f342,plain,
    ( v2_funct_1(sK6)
    | ~ spl10_22 ),
    inference(resolution,[],[f323,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP4(X0,X1) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP4(X1,X2) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP4(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f323,plain,
    ( sP4(sK5,sK6)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f321])).

fof(f337,plain,
    ( spl10_22
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f336,f144,f134,f129,f321])).

fof(f336,plain,
    ( sP4(sK5,sK6)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f335,f146])).

fof(f335,plain,
    ( ~ v1_funct_1(sK6)
    | sP4(sK5,sK6)
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f318,f136])).

fof(f318,plain,
    ( ~ v3_funct_2(sK6,sK5,sK5)
    | ~ v1_funct_1(sK6)
    | sP4(sK5,sK6)
    | ~ spl10_3 ),
    inference(resolution,[],[f105,f131])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP4(X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f38,f54])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f225,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f224,f220])).

fof(f224,plain,(
    sP9(k1_xboole_0) ),
    inference(global_subsumption,[],[f207])).

fof(f207,plain,(
    sP9(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f82,f75,f117])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f82,plain,(
    ! [X0] : v1_xboole_0(sK7(X0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(sK7(X0))
      & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f1,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK7(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f206,plain,
    ( spl10_12
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f193,f129,f196])).

fof(f193,plain,
    ( v1_relat_1(sK6)
    | ~ spl10_3 ),
    inference(resolution,[],[f91,f131])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f147,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f70,f144])).

fof(f70,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5))
      | ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    & v3_funct_2(sK6,sK5,sK5)
    & v1_funct_2(sK6,sK5,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f56])).

fof(f56,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5))
        | ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
      & v3_funct_2(sK6,sK5,sK5)
      & v1_funct_2(sK6,sK5,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f142,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f71,f139])).

fof(f71,plain,(
    v1_funct_2(sK6,sK5,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f137,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f72,f134])).

fof(f72,plain,(
    v3_funct_2(sK6,sK5,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f132,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f73,f129])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(cnf_transformation,[],[f57])).

fof(f127,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f74,f124,f120])).

fof(f74,plain,
    ( ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5))
    | ~ r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5)) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (7349)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (7341)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (7351)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (7343)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (7355)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (7342)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (7346)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (7339)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (7337)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (7338)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (7350)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (7340)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (7336)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (7345)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (7352)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (7353)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (7347)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (7356)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (7356)Refutation not found, incomplete strategy% (7356)------------------------------
% 0.21/0.52  % (7356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7356)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7356)Memory used [KB]: 10618
% 0.21/0.52  % (7356)Time elapsed: 0.102 s
% 0.21/0.52  % (7356)------------------------------
% 0.21/0.52  % (7356)------------------------------
% 0.21/0.52  % (7344)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (7348)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (7354)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.60/0.58  % (7352)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.60  % SZS output start Proof for theBenchmark
% 1.60/0.60  fof(f2783,plain,(
% 1.60/0.60    $false),
% 1.60/0.60    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f206,f225,f337,f355,f362,f439,f444,f449,f454,f459,f733,f766,f835,f854,f859,f884,f1244,f1249,f1386,f1391,f1433,f1446,f1540,f1541,f1734,f1738,f1806,f1818,f1830,f1849,f2061,f2081,f2130,f2131,f2192,f2217,f2395,f2694,f2721,f2763,f2764,f2766,f2774,f2782])).
% 1.60/0.60  fof(f2782,plain,(
% 1.60/0.60    k5_relat_1(sK6,k2_funct_1(sK6)) != k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_1(sK6)) | k2_funct_2(sK5,sK6) != k2_funct_1(sK6) | r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5)) | ~r2_relset_1(sK5,sK5,k5_relat_1(sK6,k2_funct_1(sK6)),k6_partfun1(sK5))),
% 1.60/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.60/0.60  fof(f2774,plain,(
% 1.60/0.60    spl10_81 | ~spl10_166 | ~spl10_167),
% 1.60/0.60    inference(avatar_split_clause,[],[f1831,f1647,f1642,f896])).
% 1.60/0.60  fof(f896,plain,(
% 1.60/0.60    spl10_81 <=> v1_funct_1(k2_funct_1(sK6))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).
% 1.60/0.60  fof(f1642,plain,(
% 1.60/0.60    spl10_166 <=> sP0(sK5,sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).
% 1.60/0.60  fof(f1647,plain,(
% 1.60/0.60    spl10_167 <=> k2_funct_2(sK5,sK6) = k2_funct_1(sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_167])])).
% 1.60/0.60  fof(f1831,plain,(
% 1.60/0.60    v1_funct_1(k2_funct_1(sK6)) | (~spl10_166 | ~spl10_167)),
% 1.60/0.60    inference(forward_demodulation,[],[f1786,f1649])).
% 1.60/0.60  fof(f1649,plain,(
% 1.60/0.60    k2_funct_2(sK5,sK6) = k2_funct_1(sK6) | ~spl10_167),
% 1.60/0.60    inference(avatar_component_clause,[],[f1647])).
% 1.60/0.60  fof(f1786,plain,(
% 1.60/0.60    v1_funct_1(k2_funct_2(sK5,sK6)) | ~spl10_166),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f1644,f86])).
% 1.60/0.60  fof(f86,plain,(
% 1.60/0.60    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f62])).
% 1.60/0.60  fof(f62,plain,(
% 1.60/0.60    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f48])).
% 1.60/0.60  fof(f48,plain,(
% 1.60/0.60    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 1.60/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.60/0.60  fof(f1644,plain,(
% 1.60/0.60    sP0(sK5,sK6) | ~spl10_166),
% 1.60/0.60    inference(avatar_component_clause,[],[f1642])).
% 1.60/0.60  fof(f2766,plain,(
% 1.60/0.60    k6_partfun1(sK5) != k5_relat_1(sK6,k2_funct_1(sK6)) | r2_relset_1(sK5,sK5,k5_relat_1(sK6,k2_funct_1(sK6)),k6_partfun1(sK5)) | ~r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5))),
% 1.60/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.60/0.60  fof(f2764,plain,(
% 1.60/0.60    k5_relat_1(k2_funct_1(sK6),sK6) != k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_1(sK6),sK6) | k2_funct_2(sK5,sK6) != k2_funct_1(sK6) | r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5)) | ~r2_relset_1(sK5,sK5,k5_relat_1(k2_funct_1(sK6),sK6),k6_partfun1(sK5))),
% 1.60/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.60/0.60  fof(f2763,plain,(
% 1.60/0.60    spl10_255),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f2762])).
% 1.60/0.60  fof(f2762,plain,(
% 1.60/0.60    $false | spl10_255),
% 1.60/0.60    inference(trivial_inequality_removal,[],[f2760])).
% 1.60/0.60  fof(f2760,plain,(
% 1.60/0.60    k11_relat_1(k6_partfun1(sK5),sK8(sK5,k6_partfun1(sK5),k6_partfun1(sK5))) != k11_relat_1(k6_partfun1(sK5),sK8(sK5,k6_partfun1(sK5),k6_partfun1(sK5))) | spl10_255),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f77,f77,f2439,f84])).
% 1.60/0.60  fof(f84,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k11_relat_1(X1,sK8(X0,X1,X2)) != k11_relat_1(X2,sK8(X0,X1,X2)) | r2_relset_1(X0,X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f61])).
% 1.60/0.60  fof(f61,plain,(
% 1.60/0.60    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK8(X0,X1,X2)) != k11_relat_1(X2,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.60/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f27,f60])).
% 1.60/0.60  fof(f60,plain,(
% 1.60/0.60    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK8(X0,X1,X2)) != k11_relat_1(X2,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 1.60/0.60    introduced(choice_axiom,[])).
% 1.60/0.60  fof(f27,plain,(
% 1.60/0.60    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.60/0.60    inference(flattening,[],[f26])).
% 1.60/0.60  fof(f26,plain,(
% 1.60/0.60    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.60/0.60    inference(ennf_transformation,[],[f10])).
% 1.60/0.60  fof(f10,axiom,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).
% 1.60/0.60  fof(f2439,plain,(
% 1.60/0.60    ~r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5)) | spl10_255),
% 1.60/0.60    inference(avatar_component_clause,[],[f2438])).
% 1.60/0.60  fof(f2438,plain,(
% 1.60/0.60    spl10_255 <=> r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_255])])).
% 1.60/0.60  fof(f77,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f15])).
% 1.60/0.60  fof(f15,axiom,(
% 1.60/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.60/0.60  fof(f2721,plain,(
% 1.60/0.60    ~spl10_255 | spl10_199 | ~spl10_292),
% 1.60/0.60    inference(avatar_split_clause,[],[f2706,f2691,f1911,f2438])).
% 1.60/0.60  fof(f1911,plain,(
% 1.60/0.60    spl10_199 <=> r2_relset_1(sK5,sK5,k5_relat_1(k2_funct_1(sK6),sK6),k6_partfun1(sK5))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_199])])).
% 1.60/0.60  fof(f2691,plain,(
% 1.60/0.60    spl10_292 <=> k6_partfun1(sK5) = k5_relat_1(k2_funct_1(sK6),sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_292])])).
% 1.60/0.60  fof(f2706,plain,(
% 1.60/0.60    ~r2_relset_1(sK5,sK5,k6_partfun1(sK5),k6_partfun1(sK5)) | (spl10_199 | ~spl10_292)),
% 1.60/0.60    inference(backward_demodulation,[],[f1913,f2693])).
% 1.60/0.60  fof(f2693,plain,(
% 1.60/0.60    k6_partfun1(sK5) = k5_relat_1(k2_funct_1(sK6),sK6) | ~spl10_292),
% 1.60/0.60    inference(avatar_component_clause,[],[f2691])).
% 1.60/0.60  fof(f1913,plain,(
% 1.60/0.60    ~r2_relset_1(sK5,sK5,k5_relat_1(k2_funct_1(sK6),sK6),k6_partfun1(sK5)) | spl10_199),
% 1.60/0.60    inference(avatar_component_clause,[],[f1911])).
% 1.60/0.60  fof(f2694,plain,(
% 1.60/0.60    spl10_292 | ~spl10_3 | ~spl10_5 | ~spl10_6 | ~spl10_25 | spl10_31 | ~spl10_236),
% 1.60/0.60    inference(avatar_split_clause,[],[f2675,f2214,f399,f345,f144,f139,f129,f2691])).
% 1.60/0.60  fof(f129,plain,(
% 1.60/0.60    spl10_3 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.60/0.60  fof(f139,plain,(
% 1.60/0.60    spl10_5 <=> v1_funct_2(sK6,sK5,sK5)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.60/0.60  fof(f144,plain,(
% 1.60/0.60    spl10_6 <=> v1_funct_1(sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.60/0.60  fof(f345,plain,(
% 1.60/0.60    spl10_25 <=> v2_funct_1(sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 1.60/0.60  fof(f399,plain,(
% 1.60/0.60    spl10_31 <=> k1_xboole_0 = sK5),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 1.60/0.60  fof(f2214,plain,(
% 1.60/0.60    spl10_236 <=> sK5 = k2_relset_1(sK5,sK5,sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).
% 1.60/0.60  fof(f2675,plain,(
% 1.60/0.60    k6_partfun1(sK5) = k5_relat_1(k2_funct_1(sK6),sK6) | (~spl10_3 | ~spl10_5 | ~spl10_6 | ~spl10_25 | spl10_31 | ~spl10_236)),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f146,f347,f400,f141,f131,f2216,f107])).
% 1.60/0.60  fof(f107,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f40])).
% 1.60/0.60  fof(f40,plain,(
% 1.60/0.60    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.60    inference(flattening,[],[f39])).
% 1.60/0.60  fof(f39,plain,(
% 1.60/0.60    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.60/0.60    inference(ennf_transformation,[],[f18])).
% 1.60/0.60  fof(f18,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.60/0.60  fof(f2216,plain,(
% 1.60/0.60    sK5 = k2_relset_1(sK5,sK5,sK6) | ~spl10_236),
% 1.60/0.60    inference(avatar_component_clause,[],[f2214])).
% 1.60/0.60  fof(f131,plain,(
% 1.60/0.60    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) | ~spl10_3),
% 1.60/0.60    inference(avatar_component_clause,[],[f129])).
% 1.60/0.60  fof(f141,plain,(
% 1.60/0.60    v1_funct_2(sK6,sK5,sK5) | ~spl10_5),
% 1.60/0.60    inference(avatar_component_clause,[],[f139])).
% 1.60/0.60  fof(f400,plain,(
% 1.60/0.60    k1_xboole_0 != sK5 | spl10_31),
% 1.60/0.60    inference(avatar_component_clause,[],[f399])).
% 1.60/0.60  fof(f347,plain,(
% 1.60/0.60    v2_funct_1(sK6) | ~spl10_25),
% 1.60/0.60    inference(avatar_component_clause,[],[f345])).
% 1.60/0.60  fof(f146,plain,(
% 1.60/0.60    v1_funct_1(sK6) | ~spl10_6),
% 1.60/0.60    inference(avatar_component_clause,[],[f144])).
% 1.60/0.60  fof(f2395,plain,(
% 1.60/0.60    spl10_248 | ~spl10_3 | ~spl10_5 | ~spl10_6 | ~spl10_25 | spl10_31 | ~spl10_236),
% 1.60/0.60    inference(avatar_split_clause,[],[f2387,f2214,f399,f345,f144,f139,f129,f2392])).
% 1.60/0.60  fof(f2392,plain,(
% 1.60/0.60    spl10_248 <=> k6_partfun1(sK5) = k5_relat_1(sK6,k2_funct_1(sK6))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).
% 1.60/0.60  fof(f2387,plain,(
% 1.60/0.60    k6_partfun1(sK5) = k5_relat_1(sK6,k2_funct_1(sK6)) | (~spl10_3 | ~spl10_5 | ~spl10_6 | ~spl10_25 | spl10_31 | ~spl10_236)),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f146,f347,f400,f141,f131,f2216,f106])).
% 1.60/0.60  fof(f106,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f40])).
% 1.60/0.60  fof(f2217,plain,(
% 1.60/0.60    spl10_236 | ~spl10_21 | ~spl10_233),
% 1.60/0.60    inference(avatar_split_clause,[],[f2207,f2189,f306,f2214])).
% 1.60/0.60  fof(f306,plain,(
% 1.60/0.60    spl10_21 <=> k2_relset_1(sK5,sK5,sK6) = k2_relat_1(sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.60/0.60  fof(f2189,plain,(
% 1.60/0.60    spl10_233 <=> sK5 = k2_relat_1(sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_233])])).
% 1.60/0.60  fof(f2207,plain,(
% 1.60/0.60    sK5 = k2_relset_1(sK5,sK5,sK6) | (~spl10_21 | ~spl10_233)),
% 1.60/0.60    inference(backward_demodulation,[],[f308,f2191])).
% 1.60/0.60  fof(f2191,plain,(
% 1.60/0.60    sK5 = k2_relat_1(sK6) | ~spl10_233),
% 1.60/0.60    inference(avatar_component_clause,[],[f2189])).
% 1.60/0.60  fof(f308,plain,(
% 1.60/0.60    k2_relset_1(sK5,sK5,sK6) = k2_relat_1(sK6) | ~spl10_21),
% 1.60/0.60    inference(avatar_component_clause,[],[f306])).
% 1.60/0.60  fof(f2192,plain,(
% 1.60/0.60    spl10_233 | ~spl10_27 | ~spl10_225),
% 1.60/0.60    inference(avatar_split_clause,[],[f2187,f2127,f359,f2189])).
% 1.60/0.60  fof(f359,plain,(
% 1.60/0.60    spl10_27 <=> k2_relat_1(sK6) = k1_relat_1(k2_funct_1(sK6))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 1.60/0.60  fof(f2127,plain,(
% 1.60/0.60    spl10_225 <=> sK5 = k1_relat_1(k2_funct_1(sK6))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_225])])).
% 1.60/0.60  fof(f2187,plain,(
% 1.60/0.60    sK5 = k2_relat_1(sK6) | (~spl10_27 | ~spl10_225)),
% 1.60/0.60    inference(backward_demodulation,[],[f361,f2129])).
% 1.60/0.60  fof(f2129,plain,(
% 1.60/0.60    sK5 = k1_relat_1(k2_funct_1(sK6)) | ~spl10_225),
% 1.60/0.60    inference(avatar_component_clause,[],[f2127])).
% 1.60/0.60  fof(f361,plain,(
% 1.60/0.60    k2_relat_1(sK6) = k1_relat_1(k2_funct_1(sK6)) | ~spl10_27),
% 1.60/0.60    inference(avatar_component_clause,[],[f359])).
% 1.60/0.60  fof(f2131,plain,(
% 1.60/0.60    spl10_21 | ~spl10_3),
% 1.60/0.60    inference(avatar_split_clause,[],[f1607,f129,f306])).
% 1.60/0.60  fof(f1607,plain,(
% 1.60/0.60    k2_relset_1(sK5,sK5,sK6) = k2_relat_1(sK6) | ~spl10_3),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f131,f93])).
% 1.60/0.60  fof(f93,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f34])).
% 1.60/0.60  fof(f34,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f9])).
% 1.60/0.60  fof(f9,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.60/0.60  fof(f2130,plain,(
% 1.60/0.60    spl10_225 | ~spl10_193 | ~spl10_197),
% 1.60/0.60    inference(avatar_split_clause,[],[f2099,f1846,f1815,f2127])).
% 1.60/0.60  fof(f1815,plain,(
% 1.60/0.60    spl10_193 <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_193])])).
% 1.60/0.60  fof(f1846,plain,(
% 1.60/0.60    spl10_197 <=> sK5 = k1_relset_1(sK5,sK5,k2_funct_1(sK6))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_197])])).
% 1.60/0.60  fof(f2099,plain,(
% 1.60/0.60    sK5 = k1_relat_1(k2_funct_1(sK6)) | (~spl10_193 | ~spl10_197)),
% 1.60/0.60    inference(forward_demodulation,[],[f1935,f1848])).
% 1.60/0.60  fof(f1848,plain,(
% 1.60/0.60    sK5 = k1_relset_1(sK5,sK5,k2_funct_1(sK6)) | ~spl10_197),
% 1.60/0.60    inference(avatar_component_clause,[],[f1846])).
% 1.60/0.60  fof(f1935,plain,(
% 1.60/0.60    k1_relat_1(k2_funct_1(sK6)) = k1_relset_1(sK5,sK5,k2_funct_1(sK6)) | ~spl10_193),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f1817,f92])).
% 1.60/0.60  fof(f92,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f33])).
% 1.60/0.60  fof(f33,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f8])).
% 1.60/0.60  fof(f8,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.60/0.60  fof(f1817,plain,(
% 1.60/0.60    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) | ~spl10_193),
% 1.60/0.60    inference(avatar_component_clause,[],[f1815])).
% 1.60/0.60  fof(f2081,plain,(
% 1.60/0.60    spl10_220 | ~spl10_3 | ~spl10_6 | ~spl10_81 | ~spl10_193),
% 1.60/0.60    inference(avatar_split_clause,[],[f1943,f1815,f896,f144,f129,f2078])).
% 1.60/0.60  fof(f2078,plain,(
% 1.60/0.60    spl10_220 <=> k5_relat_1(k2_funct_1(sK6),sK6) = k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_1(sK6),sK6)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_220])])).
% 1.60/0.60  fof(f1943,plain,(
% 1.60/0.60    k5_relat_1(k2_funct_1(sK6),sK6) = k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_1(sK6),sK6) | (~spl10_3 | ~spl10_6 | ~spl10_81 | ~spl10_193)),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f146,f898,f131,f1817,f110])).
% 1.60/0.60  fof(f110,plain,(
% 1.60/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f45])).
% 1.60/0.60  fof(f45,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.60/0.60    inference(flattening,[],[f44])).
% 1.60/0.60  fof(f44,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.60/0.60    inference(ennf_transformation,[],[f16])).
% 1.60/0.60  fof(f16,axiom,(
% 1.60/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.60/0.60  fof(f898,plain,(
% 1.60/0.60    v1_funct_1(k2_funct_1(sK6)) | ~spl10_81),
% 1.60/0.60    inference(avatar_component_clause,[],[f896])).
% 1.60/0.60  fof(f2061,plain,(
% 1.60/0.60    spl10_216 | ~spl10_3 | ~spl10_6 | ~spl10_81 | ~spl10_193),
% 1.60/0.60    inference(avatar_split_clause,[],[f1947,f1815,f896,f144,f129,f2058])).
% 1.60/0.60  fof(f2058,plain,(
% 1.60/0.60    spl10_216 <=> k5_relat_1(sK6,k2_funct_1(sK6)) = k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_1(sK6))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).
% 1.60/0.60  fof(f1947,plain,(
% 1.60/0.60    k5_relat_1(sK6,k2_funct_1(sK6)) = k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_1(sK6)) | (~spl10_3 | ~spl10_6 | ~spl10_81 | ~spl10_193)),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f146,f131,f898,f1817,f110])).
% 1.60/0.60  fof(f1849,plain,(
% 1.60/0.60    spl10_197 | spl10_31 | ~spl10_191 | ~spl10_195),
% 1.60/0.60    inference(avatar_split_clause,[],[f1844,f1827,f1803,f399,f1846])).
% 1.60/0.60  fof(f1803,plain,(
% 1.60/0.60    spl10_191 <=> sP2(sK5,k2_funct_1(sK6),sK5)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).
% 1.60/0.60  fof(f1827,plain,(
% 1.60/0.60    spl10_195 <=> v1_funct_2(k2_funct_1(sK6),sK5,sK5)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_195])])).
% 1.60/0.60  fof(f1844,plain,(
% 1.60/0.60    sK5 = k1_relset_1(sK5,sK5,k2_funct_1(sK6)) | (spl10_31 | ~spl10_191 | ~spl10_195)),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f1590,f1805,f1829,f96])).
% 1.60/0.60  fof(f96,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f66])).
% 1.60/0.60  fof(f66,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 1.60/0.60    inference(rectify,[],[f65])).
% 1.60/0.60  fof(f65,plain,(
% 1.60/0.60    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f51])).
% 1.60/0.60  fof(f51,plain,(
% 1.60/0.60    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.60/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.60/0.60  fof(f1829,plain,(
% 1.60/0.60    v1_funct_2(k2_funct_1(sK6),sK5,sK5) | ~spl10_195),
% 1.60/0.60    inference(avatar_component_clause,[],[f1827])).
% 1.60/0.60  fof(f1805,plain,(
% 1.60/0.60    sP2(sK5,k2_funct_1(sK6),sK5) | ~spl10_191),
% 1.60/0.60    inference(avatar_component_clause,[],[f1803])).
% 1.60/0.60  fof(f1590,plain,(
% 1.60/0.60    ( ! [X0] : (~sP1(X0,sK5)) ) | spl10_31),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f400,f98])).
% 1.60/0.60  fof(f98,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 1.60/0.60    inference(cnf_transformation,[],[f67])).
% 1.60/0.60  fof(f67,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f50])).
% 1.60/0.60  fof(f50,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.60/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.60/0.60  fof(f1830,plain,(
% 1.60/0.60    spl10_195 | ~spl10_166 | ~spl10_167),
% 1.60/0.60    inference(avatar_split_clause,[],[f1825,f1647,f1642,f1827])).
% 1.60/0.60  fof(f1825,plain,(
% 1.60/0.60    v1_funct_2(k2_funct_1(sK6),sK5,sK5) | (~spl10_166 | ~spl10_167)),
% 1.60/0.60    inference(forward_demodulation,[],[f1787,f1649])).
% 1.60/0.60  fof(f1787,plain,(
% 1.60/0.60    v1_funct_2(k2_funct_2(sK5,sK6),sK5,sK5) | ~spl10_166),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f1644,f87])).
% 1.60/0.60  fof(f87,plain,(
% 1.60/0.60    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~sP0(X0,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f62])).
% 1.60/0.60  fof(f1818,plain,(
% 1.60/0.60    spl10_193 | ~spl10_166 | ~spl10_167),
% 1.60/0.60    inference(avatar_split_clause,[],[f1813,f1647,f1642,f1815])).
% 1.60/0.60  fof(f1813,plain,(
% 1.60/0.60    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) | (~spl10_166 | ~spl10_167)),
% 1.60/0.60    inference(forward_demodulation,[],[f1789,f1649])).
% 1.60/0.60  fof(f1789,plain,(
% 1.60/0.60    m1_subset_1(k2_funct_2(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) | ~spl10_166),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f1644,f89])).
% 1.60/0.60  fof(f89,plain,(
% 1.60/0.60    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f62])).
% 1.60/0.60  fof(f1806,plain,(
% 1.60/0.60    spl10_191 | ~spl10_166 | ~spl10_167),
% 1.60/0.60    inference(avatar_split_clause,[],[f1801,f1647,f1642,f1803])).
% 1.60/0.60  fof(f1801,plain,(
% 1.60/0.60    sP2(sK5,k2_funct_1(sK6),sK5) | (~spl10_166 | ~spl10_167)),
% 1.60/0.60    inference(forward_demodulation,[],[f1791,f1649])).
% 1.60/0.60  fof(f1791,plain,(
% 1.60/0.60    sP2(sK5,k2_funct_2(sK5,sK6),sK5) | ~spl10_166),
% 1.60/0.60    inference(unit_resulting_resolution,[],[f1644,f282])).
% 1.60/0.60  fof(f282,plain,(
% 1.60/0.60    ( ! [X2,X3] : (sP2(X2,k2_funct_2(X2,X3),X2) | ~sP0(X2,X3)) )),
% 1.60/0.60    inference(resolution,[],[f89,f100])).
% 1.60/0.60  fof(f100,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f53])).
% 1.60/0.60  fof(f53,plain,(
% 1.60/0.60    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(definition_folding,[],[f36,f52,f51,f50])).
% 1.60/0.60  fof(f52,plain,(
% 1.60/0.60    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 1.60/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.60/0.60  fof(f36,plain,(
% 1.60/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(flattening,[],[f35])).
% 1.60/0.60  fof(f35,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f12])).
% 1.60/0.60  fof(f12,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.60/0.60  fof(f1738,plain,(
% 1.60/0.60    spl10_166 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6),
% 1.60/0.60    inference(avatar_split_clause,[],[f1737,f144,f139,f134,f129,f1642])).
% 1.60/0.60  fof(f134,plain,(
% 1.60/0.60    spl10_4 <=> v3_funct_2(sK6,sK5,sK5)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.60/0.60  fof(f1737,plain,(
% 1.60/0.60    sP0(sK5,sK6) | (~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.60/0.60    inference(subsumption_resolution,[],[f1736,f146])).
% 1.60/0.60  fof(f1736,plain,(
% 1.60/0.60    sP0(sK5,sK6) | ~v1_funct_1(sK6) | (~spl10_3 | ~spl10_4 | ~spl10_5)),
% 1.60/0.60    inference(subsumption_resolution,[],[f1735,f141])).
% 1.60/0.60  fof(f1735,plain,(
% 1.60/0.60    sP0(sK5,sK6) | ~v1_funct_2(sK6,sK5,sK5) | ~v1_funct_1(sK6) | (~spl10_3 | ~spl10_4)),
% 1.60/0.60    inference(subsumption_resolution,[],[f1637,f136])).
% 1.60/0.60  fof(f136,plain,(
% 1.60/0.60    v3_funct_2(sK6,sK5,sK5) | ~spl10_4),
% 1.60/0.60    inference(avatar_component_clause,[],[f134])).
% 1.60/0.60  fof(f1637,plain,(
% 1.60/0.60    sP0(sK5,sK6) | ~v3_funct_2(sK6,sK5,sK5) | ~v1_funct_2(sK6,sK5,sK5) | ~v1_funct_1(sK6) | ~spl10_3),
% 1.60/0.60    inference(resolution,[],[f131,f90])).
% 1.60/0.60  fof(f90,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | sP0(X0,X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f49])).
% 1.60/0.60  fof(f49,plain,(
% 1.60/0.60    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.60/0.60    inference(definition_folding,[],[f31,f48])).
% 1.60/0.60  fof(f31,plain,(
% 1.60/0.60    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.60/0.60    inference(flattening,[],[f30])).
% 1.60/0.61  fof(f30,plain,(
% 1.60/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.60/0.61    inference(ennf_transformation,[],[f14])).
% 1.60/0.61  fof(f14,axiom,(
% 1.60/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.60/0.61  fof(f1734,plain,(
% 1.60/0.61    spl10_167 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6),
% 1.60/0.61    inference(avatar_split_clause,[],[f1733,f144,f139,f134,f129,f1647])).
% 1.60/0.61  fof(f1733,plain,(
% 1.60/0.61    k2_funct_2(sK5,sK6) = k2_funct_1(sK6) | (~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.60/0.61    inference(subsumption_resolution,[],[f1732,f146])).
% 1.60/0.61  fof(f1732,plain,(
% 1.60/0.61    k2_funct_2(sK5,sK6) = k2_funct_1(sK6) | ~v1_funct_1(sK6) | (~spl10_3 | ~spl10_4 | ~spl10_5)),
% 1.60/0.61    inference(subsumption_resolution,[],[f1731,f141])).
% 1.60/0.61  fof(f1731,plain,(
% 1.60/0.61    k2_funct_2(sK5,sK6) = k2_funct_1(sK6) | ~v1_funct_2(sK6,sK5,sK5) | ~v1_funct_1(sK6) | (~spl10_3 | ~spl10_4)),
% 1.60/0.61    inference(subsumption_resolution,[],[f1636,f136])).
% 1.60/0.61  fof(f1636,plain,(
% 1.60/0.61    k2_funct_2(sK5,sK6) = k2_funct_1(sK6) | ~v3_funct_2(sK6,sK5,sK5) | ~v1_funct_2(sK6,sK5,sK5) | ~v1_funct_1(sK6) | ~spl10_3),
% 1.60/0.61    inference(resolution,[],[f131,f85])).
% 1.60/0.61  fof(f85,plain,(
% 1.60/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f29])).
% 1.60/0.61  fof(f29,plain,(
% 1.60/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.60/0.61    inference(flattening,[],[f28])).
% 1.60/0.61  fof(f28,plain,(
% 1.60/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.60/0.61    inference(ennf_transformation,[],[f17])).
% 1.60/0.61  fof(f17,axiom,(
% 1.60/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.60/0.61  fof(f1541,plain,(
% 1.60/0.61    spl10_156 | ~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81 | ~spl10_147),
% 1.60/0.61    inference(avatar_split_clause,[],[f1487,f1383,f896,f881,f446,f144,f1443])).
% 1.60/0.61  fof(f1443,plain,(
% 1.60/0.61    spl10_156 <=> m1_subset_1(k5_relat_1(k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).
% 1.60/0.61  fof(f446,plain,(
% 1.60/0.61    spl10_36 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 1.60/0.61  fof(f881,plain,(
% 1.60/0.61    spl10_78 <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).
% 1.60/0.61  fof(f1383,plain,(
% 1.60/0.61    spl10_147 <=> k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6) = k5_relat_1(k2_funct_1(sK6),sK6)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_147])])).
% 1.60/0.61  fof(f1487,plain,(
% 1.60/0.61    m1_subset_1(k5_relat_1(k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81 | ~spl10_147)),
% 1.60/0.61    inference(forward_demodulation,[],[f1468,f1385])).
% 1.60/0.61  fof(f1385,plain,(
% 1.60/0.61    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6) = k5_relat_1(k2_funct_1(sK6),sK6) | ~spl10_147),
% 1.60/0.61    inference(avatar_component_clause,[],[f1383])).
% 1.60/0.61  fof(f1468,plain,(
% 1.60/0.61    m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f146,f898,f883,f448,f112])).
% 1.60/0.61  fof(f112,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f47])).
% 1.60/0.61  fof(f47,plain,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.60/0.61    inference(flattening,[],[f46])).
% 1.60/0.61  fof(f46,plain,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.60/0.61    inference(ennf_transformation,[],[f13])).
% 1.60/0.61  fof(f13,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.60/0.61  fof(f448,plain,(
% 1.60/0.61    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl10_36),
% 1.60/0.61    inference(avatar_component_clause,[],[f446])).
% 1.60/0.61  fof(f883,plain,(
% 1.60/0.61    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl10_78),
% 1.60/0.61    inference(avatar_component_clause,[],[f881])).
% 1.60/0.61  fof(f1540,plain,(
% 1.60/0.61    spl10_154 | ~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81 | ~spl10_148),
% 1.60/0.61    inference(avatar_split_clause,[],[f1490,f1388,f896,f881,f446,f144,f1430])).
% 1.60/0.61  fof(f1430,plain,(
% 1.60/0.61    spl10_154 <=> m1_subset_1(k5_relat_1(sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).
% 1.60/0.61  fof(f1388,plain,(
% 1.60/0.61    spl10_148 <=> k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)) = k5_relat_1(sK6,k2_funct_1(sK6))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).
% 1.60/0.61  fof(f1490,plain,(
% 1.60/0.61    m1_subset_1(k5_relat_1(sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81 | ~spl10_148)),
% 1.60/0.61    inference(forward_demodulation,[],[f1467,f1390])).
% 1.60/0.61  fof(f1390,plain,(
% 1.60/0.61    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)) = k5_relat_1(sK6,k2_funct_1(sK6)) | ~spl10_148),
% 1.60/0.61    inference(avatar_component_clause,[],[f1388])).
% 1.60/0.61  fof(f1467,plain,(
% 1.60/0.61    m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f146,f448,f898,f883,f112])).
% 1.60/0.61  fof(f1446,plain,(
% 1.60/0.61    ~spl10_156 | spl10_122 | ~spl10_147),
% 1.60/0.61    inference(avatar_split_clause,[],[f1435,f1383,f1241,f1443])).
% 1.60/0.61  fof(f1241,plain,(
% 1.60/0.61    spl10_122 <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).
% 1.60/0.61  fof(f1435,plain,(
% 1.60/0.61    ~m1_subset_1(k5_relat_1(k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl10_122 | ~spl10_147)),
% 1.60/0.61    inference(backward_demodulation,[],[f1243,f1385])).
% 1.60/0.61  fof(f1243,plain,(
% 1.60/0.61    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl10_122),
% 1.60/0.61    inference(avatar_component_clause,[],[f1241])).
% 1.60/0.61  fof(f1433,plain,(
% 1.60/0.61    ~spl10_154 | spl10_123 | ~spl10_148),
% 1.60/0.61    inference(avatar_split_clause,[],[f1422,f1388,f1246,f1430])).
% 1.60/0.61  fof(f1246,plain,(
% 1.60/0.61    spl10_123 <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).
% 1.60/0.61  fof(f1422,plain,(
% 1.60/0.61    ~m1_subset_1(k5_relat_1(sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl10_123 | ~spl10_148)),
% 1.60/0.61    inference(backward_demodulation,[],[f1248,f1390])).
% 1.60/0.61  fof(f1248,plain,(
% 1.60/0.61    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl10_123),
% 1.60/0.61    inference(avatar_component_clause,[],[f1246])).
% 1.60/0.61  fof(f1391,plain,(
% 1.60/0.61    spl10_148 | ~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81),
% 1.60/0.61    inference(avatar_split_clause,[],[f1370,f896,f881,f446,f144,f1388])).
% 1.60/0.61  fof(f1370,plain,(
% 1.60/0.61    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)) = k5_relat_1(sK6,k2_funct_1(sK6)) | (~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f146,f448,f898,f883,f110])).
% 1.60/0.61  fof(f1386,plain,(
% 1.60/0.61    spl10_147 | ~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81),
% 1.60/0.61    inference(avatar_split_clause,[],[f1371,f896,f881,f446,f144,f1383])).
% 1.60/0.61  fof(f1371,plain,(
% 1.60/0.61    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6) = k5_relat_1(k2_funct_1(sK6),sK6) | (~spl10_6 | ~spl10_36 | ~spl10_78 | ~spl10_81)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f146,f898,f883,f448,f110])).
% 1.60/0.61  fof(f1249,plain,(
% 1.60/0.61    ~spl10_123 | ~spl10_15 | spl10_72),
% 1.60/0.61    inference(avatar_split_clause,[],[f1130,f851,f220,f1246])).
% 1.60/0.61  fof(f220,plain,(
% 1.60/0.61    spl10_15 <=> sP9(k1_xboole_0)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.60/0.61  fof(f851,plain,(
% 1.60/0.61    spl10_72 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k6_partfun1(k1_xboole_0))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).
% 1.60/0.61  fof(f1130,plain,(
% 1.60/0.61    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_15 | spl10_72)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f853,f226,f77,f83])).
% 1.60/0.61  fof(f83,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X0) | r2_relset_1(X0,X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f61])).
% 1.60/0.61  fof(f226,plain,(
% 1.60/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl10_15),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f222,f118])).
% 1.60/0.61  fof(f118,plain,(
% 1.60/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 1.60/0.61    inference(general_splitting,[],[f109,f117_D])).
% 1.60/0.61  fof(f117,plain,(
% 1.60/0.61    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP9(X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f117_D])).
% 1.60/0.61  fof(f117_D,plain,(
% 1.60/0.61    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP9(X1)) )),
% 1.60/0.61    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 1.60/0.61  fof(f109,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f43])).
% 1.60/0.61  fof(f43,plain,(
% 1.60/0.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.60/0.61    inference(ennf_transformation,[],[f5])).
% 1.60/0.61  fof(f5,axiom,(
% 1.60/0.61    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.60/0.61  fof(f222,plain,(
% 1.60/0.61    sP9(k1_xboole_0) | ~spl10_15),
% 1.60/0.61    inference(avatar_component_clause,[],[f220])).
% 1.60/0.61  fof(f853,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k6_partfun1(k1_xboole_0)) | spl10_72),
% 1.60/0.61    inference(avatar_component_clause,[],[f851])).
% 1.60/0.61  fof(f1244,plain,(
% 1.60/0.61    ~spl10_122 | ~spl10_15 | spl10_73),
% 1.60/0.61    inference(avatar_split_clause,[],[f1131,f856,f220,f1241])).
% 1.60/0.61  fof(f856,plain,(
% 1.60/0.61    spl10_73 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k6_partfun1(k1_xboole_0))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).
% 1.60/0.61  fof(f1131,plain,(
% 1.60/0.61    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_15 | spl10_73)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f858,f226,f77,f83])).
% 1.60/0.61  fof(f858,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k6_partfun1(k1_xboole_0)) | spl10_73),
% 1.60/0.61    inference(avatar_component_clause,[],[f856])).
% 1.60/0.61  fof(f884,plain,(
% 1.60/0.61    spl10_78 | ~spl10_63 | ~spl10_71),
% 1.60/0.61    inference(avatar_split_clause,[],[f842,f825,f763,f881])).
% 1.60/0.61  fof(f763,plain,(
% 1.60/0.61    spl10_63 <=> m1_subset_1(k2_funct_2(k1_xboole_0,sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).
% 1.60/0.61  fof(f825,plain,(
% 1.60/0.61    spl10_71 <=> k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).
% 1.60/0.61  fof(f842,plain,(
% 1.60/0.61    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_63 | ~spl10_71)),
% 1.60/0.61    inference(backward_demodulation,[],[f765,f827])).
% 1.60/0.61  fof(f827,plain,(
% 1.60/0.61    k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6) | ~spl10_71),
% 1.60/0.61    inference(avatar_component_clause,[],[f825])).
% 1.60/0.61  fof(f765,plain,(
% 1.60/0.61    m1_subset_1(k2_funct_2(k1_xboole_0,sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl10_63),
% 1.60/0.61    inference(avatar_component_clause,[],[f763])).
% 1.60/0.61  fof(f859,plain,(
% 1.60/0.61    ~spl10_73 | spl10_35 | ~spl10_71),
% 1.60/0.61    inference(avatar_split_clause,[],[f837,f825,f441,f856])).
% 1.60/0.61  fof(f441,plain,(
% 1.60/0.61    spl10_35 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,sK6),sK6),k6_partfun1(k1_xboole_0))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 1.60/0.61  fof(f837,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK6),sK6),k6_partfun1(k1_xboole_0)) | (spl10_35 | ~spl10_71)),
% 1.60/0.61    inference(backward_demodulation,[],[f443,f827])).
% 1.60/0.61  fof(f443,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,sK6),sK6),k6_partfun1(k1_xboole_0)) | spl10_35),
% 1.60/0.61    inference(avatar_component_clause,[],[f441])).
% 1.60/0.61  fof(f854,plain,(
% 1.60/0.61    ~spl10_72 | spl10_34 | ~spl10_71),
% 1.60/0.61    inference(avatar_split_clause,[],[f836,f825,f436,f851])).
% 1.60/0.61  fof(f436,plain,(
% 1.60/0.61    spl10_34 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_2(k1_xboole_0,sK6)),k6_partfun1(k1_xboole_0))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 1.60/0.61  fof(f836,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_1(sK6)),k6_partfun1(k1_xboole_0)) | (spl10_34 | ~spl10_71)),
% 1.60/0.61    inference(backward_demodulation,[],[f438,f827])).
% 1.60/0.61  fof(f438,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_2(k1_xboole_0,sK6)),k6_partfun1(k1_xboole_0)) | spl10_34),
% 1.60/0.61    inference(avatar_component_clause,[],[f436])).
% 1.60/0.61  fof(f835,plain,(
% 1.60/0.61    spl10_71 | ~spl10_6 | ~spl10_36 | ~spl10_37 | ~spl10_38),
% 1.60/0.61    inference(avatar_split_clause,[],[f834,f456,f451,f446,f144,f825])).
% 1.60/0.61  fof(f451,plain,(
% 1.60/0.61    spl10_37 <=> v3_funct_2(sK6,k1_xboole_0,k1_xboole_0)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 1.60/0.61  fof(f456,plain,(
% 1.60/0.61    spl10_38 <=> v1_funct_2(sK6,k1_xboole_0,k1_xboole_0)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 1.60/0.61  fof(f834,plain,(
% 1.60/0.61    k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6) | (~spl10_6 | ~spl10_36 | ~spl10_37 | ~spl10_38)),
% 1.60/0.61    inference(subsumption_resolution,[],[f833,f146])).
% 1.60/0.61  fof(f833,plain,(
% 1.60/0.61    k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6) | ~v1_funct_1(sK6) | (~spl10_36 | ~spl10_37 | ~spl10_38)),
% 1.60/0.61    inference(subsumption_resolution,[],[f832,f458])).
% 1.60/0.61  fof(f458,plain,(
% 1.60/0.61    v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~spl10_38),
% 1.60/0.61    inference(avatar_component_clause,[],[f456])).
% 1.60/0.61  fof(f832,plain,(
% 1.60/0.61    k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6) | ~v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK6) | (~spl10_36 | ~spl10_37)),
% 1.60/0.61    inference(subsumption_resolution,[],[f822,f453])).
% 1.60/0.61  fof(f453,plain,(
% 1.60/0.61    v3_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~spl10_37),
% 1.60/0.61    inference(avatar_component_clause,[],[f451])).
% 1.60/0.61  fof(f822,plain,(
% 1.60/0.61    k2_funct_1(sK6) = k2_funct_2(k1_xboole_0,sK6) | ~v3_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK6) | ~spl10_36),
% 1.60/0.61    inference(resolution,[],[f85,f448])).
% 1.60/0.61  fof(f766,plain,(
% 1.60/0.61    spl10_63 | ~spl10_58),
% 1.60/0.61    inference(avatar_split_clause,[],[f737,f723,f763])).
% 1.60/0.61  fof(f723,plain,(
% 1.60/0.61    spl10_58 <=> sP0(k1_xboole_0,sK6)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 1.60/0.61  fof(f737,plain,(
% 1.60/0.61    m1_subset_1(k2_funct_2(k1_xboole_0,sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl10_58),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f725,f89])).
% 1.60/0.61  fof(f725,plain,(
% 1.60/0.61    sP0(k1_xboole_0,sK6) | ~spl10_58),
% 1.60/0.61    inference(avatar_component_clause,[],[f723])).
% 1.60/0.61  fof(f733,plain,(
% 1.60/0.61    spl10_58 | ~spl10_6 | ~spl10_36 | ~spl10_37 | ~spl10_38),
% 1.60/0.61    inference(avatar_split_clause,[],[f732,f456,f451,f446,f144,f723])).
% 1.60/0.61  fof(f732,plain,(
% 1.60/0.61    sP0(k1_xboole_0,sK6) | (~spl10_6 | ~spl10_36 | ~spl10_37 | ~spl10_38)),
% 1.60/0.61    inference(subsumption_resolution,[],[f731,f146])).
% 1.60/0.61  fof(f731,plain,(
% 1.60/0.61    sP0(k1_xboole_0,sK6) | ~v1_funct_1(sK6) | (~spl10_36 | ~spl10_37 | ~spl10_38)),
% 1.60/0.61    inference(subsumption_resolution,[],[f730,f458])).
% 1.60/0.61  fof(f730,plain,(
% 1.60/0.61    sP0(k1_xboole_0,sK6) | ~v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK6) | (~spl10_36 | ~spl10_37)),
% 1.60/0.61    inference(subsumption_resolution,[],[f720,f453])).
% 1.60/0.61  fof(f720,plain,(
% 1.60/0.61    sP0(k1_xboole_0,sK6) | ~v3_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK6) | ~spl10_36),
% 1.60/0.61    inference(resolution,[],[f90,f448])).
% 1.60/0.61  fof(f459,plain,(
% 1.60/0.61    spl10_38 | ~spl10_5 | ~spl10_31),
% 1.60/0.61    inference(avatar_split_clause,[],[f420,f399,f139,f456])).
% 1.60/0.61  fof(f420,plain,(
% 1.60/0.61    v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) | (~spl10_5 | ~spl10_31)),
% 1.60/0.61    inference(backward_demodulation,[],[f141,f401])).
% 1.60/0.61  fof(f401,plain,(
% 1.60/0.61    k1_xboole_0 = sK5 | ~spl10_31),
% 1.60/0.61    inference(avatar_component_clause,[],[f399])).
% 1.60/0.61  fof(f454,plain,(
% 1.60/0.61    spl10_37 | ~spl10_4 | ~spl10_31),
% 1.60/0.61    inference(avatar_split_clause,[],[f419,f399,f134,f451])).
% 1.60/0.61  fof(f419,plain,(
% 1.60/0.61    v3_funct_2(sK6,k1_xboole_0,k1_xboole_0) | (~spl10_4 | ~spl10_31)),
% 1.60/0.61    inference(backward_demodulation,[],[f136,f401])).
% 1.60/0.61  fof(f449,plain,(
% 1.60/0.61    spl10_36 | ~spl10_3 | ~spl10_31),
% 1.60/0.61    inference(avatar_split_clause,[],[f418,f399,f129,f446])).
% 1.60/0.61  fof(f418,plain,(
% 1.60/0.61    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl10_3 | ~spl10_31)),
% 1.60/0.61    inference(backward_demodulation,[],[f131,f401])).
% 1.60/0.61  fof(f444,plain,(
% 1.60/0.61    ~spl10_35 | spl10_2 | ~spl10_31),
% 1.60/0.61    inference(avatar_split_clause,[],[f417,f399,f124,f441])).
% 1.60/0.61  fof(f124,plain,(
% 1.60/0.61    spl10_2 <=> r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.60/0.61  fof(f417,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,sK6),sK6),k6_partfun1(k1_xboole_0)) | (spl10_2 | ~spl10_31)),
% 1.60/0.61    inference(backward_demodulation,[],[f126,f401])).
% 1.60/0.61  fof(f126,plain,(
% 1.60/0.61    ~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5)) | spl10_2),
% 1.60/0.61    inference(avatar_component_clause,[],[f124])).
% 1.60/0.61  fof(f439,plain,(
% 1.60/0.61    ~spl10_34 | spl10_1 | ~spl10_31),
% 1.60/0.61    inference(avatar_split_clause,[],[f416,f399,f120,f436])).
% 1.60/0.61  fof(f120,plain,(
% 1.60/0.61    spl10_1 <=> r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.60/0.61  fof(f416,plain,(
% 1.60/0.61    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6,k2_funct_2(k1_xboole_0,sK6)),k6_partfun1(k1_xboole_0)) | (spl10_1 | ~spl10_31)),
% 1.60/0.61    inference(backward_demodulation,[],[f122,f401])).
% 1.60/0.61  fof(f122,plain,(
% 1.60/0.61    ~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5)) | spl10_1),
% 1.60/0.61    inference(avatar_component_clause,[],[f120])).
% 1.60/0.61  fof(f362,plain,(
% 1.60/0.61    spl10_27 | ~spl10_6 | ~spl10_12 | ~spl10_25),
% 1.60/0.61    inference(avatar_split_clause,[],[f357,f345,f196,f144,f359])).
% 1.60/0.61  fof(f196,plain,(
% 1.60/0.61    spl10_12 <=> v1_relat_1(sK6)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.60/0.61  fof(f357,plain,(
% 1.60/0.61    k2_relat_1(sK6) = k1_relat_1(k2_funct_1(sK6)) | (~spl10_6 | ~spl10_12 | ~spl10_25)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f198,f146,f347,f79])).
% 1.60/0.61  fof(f79,plain,(
% 1.60/0.61    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f25])).
% 1.60/0.61  fof(f25,plain,(
% 1.60/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.61    inference(flattening,[],[f24])).
% 1.60/0.61  fof(f24,plain,(
% 1.60/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.61    inference(ennf_transformation,[],[f6])).
% 1.60/0.61  fof(f6,axiom,(
% 1.60/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.60/0.61  fof(f198,plain,(
% 1.60/0.61    v1_relat_1(sK6) | ~spl10_12),
% 1.60/0.61    inference(avatar_component_clause,[],[f196])).
% 1.60/0.61  fof(f355,plain,(
% 1.60/0.61    spl10_25 | ~spl10_22),
% 1.60/0.61    inference(avatar_split_clause,[],[f342,f321,f345])).
% 1.60/0.61  fof(f321,plain,(
% 1.60/0.61    spl10_22 <=> sP4(sK5,sK6)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.60/0.61  fof(f342,plain,(
% 1.60/0.61    v2_funct_1(sK6) | ~spl10_22),
% 1.60/0.61    inference(resolution,[],[f323,f103])).
% 1.60/0.61  fof(f103,plain,(
% 1.60/0.61    ( ! [X0,X1] : (~sP4(X0,X1) | v2_funct_1(X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f69])).
% 1.60/0.61  fof(f69,plain,(
% 1.60/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP4(X0,X1))),
% 1.60/0.61    inference(rectify,[],[f68])).
% 1.60/0.61  fof(f68,plain,(
% 1.60/0.61    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP4(X1,X2))),
% 1.60/0.61    inference(nnf_transformation,[],[f54])).
% 1.60/0.61  fof(f54,plain,(
% 1.60/0.61    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP4(X1,X2))),
% 1.60/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.60/0.61  fof(f323,plain,(
% 1.60/0.61    sP4(sK5,sK6) | ~spl10_22),
% 1.60/0.61    inference(avatar_component_clause,[],[f321])).
% 1.60/0.61  fof(f337,plain,(
% 1.60/0.61    spl10_22 | ~spl10_3 | ~spl10_4 | ~spl10_6),
% 1.60/0.61    inference(avatar_split_clause,[],[f336,f144,f134,f129,f321])).
% 1.60/0.61  fof(f336,plain,(
% 1.60/0.61    sP4(sK5,sK6) | (~spl10_3 | ~spl10_4 | ~spl10_6)),
% 1.60/0.61    inference(subsumption_resolution,[],[f335,f146])).
% 1.60/0.61  fof(f335,plain,(
% 1.60/0.61    ~v1_funct_1(sK6) | sP4(sK5,sK6) | (~spl10_3 | ~spl10_4)),
% 1.60/0.61    inference(subsumption_resolution,[],[f318,f136])).
% 1.60/0.61  fof(f318,plain,(
% 1.60/0.61    ~v3_funct_2(sK6,sK5,sK5) | ~v1_funct_1(sK6) | sP4(sK5,sK6) | ~spl10_3),
% 1.60/0.61    inference(resolution,[],[f105,f131])).
% 1.60/0.61  fof(f105,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP4(X1,X2)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f55])).
% 1.60/0.61  fof(f55,plain,(
% 1.60/0.61    ! [X0,X1,X2] : (sP4(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.61    inference(definition_folding,[],[f38,f54])).
% 1.60/0.61  fof(f38,plain,(
% 1.60/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.61    inference(flattening,[],[f37])).
% 1.60/0.61  fof(f37,plain,(
% 1.60/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.61    inference(ennf_transformation,[],[f11])).
% 1.60/0.61  fof(f11,axiom,(
% 1.60/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.60/0.61  fof(f225,plain,(
% 1.60/0.61    spl10_15),
% 1.60/0.61    inference(avatar_split_clause,[],[f224,f220])).
% 1.60/0.61  fof(f224,plain,(
% 1.60/0.61    sP9(k1_xboole_0)),
% 1.60/0.61    inference(global_subsumption,[],[f207])).
% 1.60/0.61  fof(f207,plain,(
% 1.60/0.61    sP9(k1_xboole_0)),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f82,f75,f117])).
% 1.60/0.61  fof(f75,plain,(
% 1.60/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f2])).
% 1.60/0.61  fof(f2,axiom,(
% 1.60/0.61    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.60/0.61  fof(f82,plain,(
% 1.60/0.61    ( ! [X0] : (v1_xboole_0(sK7(X0))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f59])).
% 1.60/0.61  fof(f59,plain,(
% 1.60/0.61    ! [X0] : (v1_xboole_0(sK7(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)))),
% 1.60/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f1,f58])).
% 1.60/0.61  fof(f58,plain,(
% 1.60/0.61    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK7(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(X0))))),
% 1.60/0.61    introduced(choice_axiom,[])).
% 1.60/0.61  fof(f1,axiom,(
% 1.60/0.61    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.60/0.61  fof(f206,plain,(
% 1.60/0.61    spl10_12 | ~spl10_3),
% 1.60/0.61    inference(avatar_split_clause,[],[f193,f129,f196])).
% 1.60/0.61  fof(f193,plain,(
% 1.60/0.61    v1_relat_1(sK6) | ~spl10_3),
% 1.60/0.61    inference(resolution,[],[f91,f131])).
% 1.60/0.61  fof(f91,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f32])).
% 1.60/0.61  fof(f32,plain,(
% 1.60/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.61    inference(ennf_transformation,[],[f7])).
% 1.60/0.61  fof(f7,axiom,(
% 1.60/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.60/0.61  fof(f147,plain,(
% 1.60/0.61    spl10_6),
% 1.60/0.61    inference(avatar_split_clause,[],[f70,f144])).
% 1.60/0.61  fof(f70,plain,(
% 1.60/0.61    v1_funct_1(sK6)),
% 1.60/0.61    inference(cnf_transformation,[],[f57])).
% 1.60/0.61  fof(f57,plain,(
% 1.60/0.61    (~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5)) | ~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) & v3_funct_2(sK6,sK5,sK5) & v1_funct_2(sK6,sK5,sK5) & v1_funct_1(sK6)),
% 1.60/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f56])).
% 1.60/0.61  fof(f56,plain,(
% 1.60/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5)) | ~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) & v3_funct_2(sK6,sK5,sK5) & v1_funct_2(sK6,sK5,sK5) & v1_funct_1(sK6))),
% 1.60/0.61    introduced(choice_axiom,[])).
% 1.60/0.61  fof(f22,plain,(
% 1.60/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.60/0.61    inference(flattening,[],[f21])).
% 1.60/0.61  fof(f21,plain,(
% 1.60/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.60/0.61    inference(ennf_transformation,[],[f20])).
% 1.60/0.61  fof(f20,negated_conjecture,(
% 1.60/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.60/0.61    inference(negated_conjecture,[],[f19])).
% 1.60/0.61  fof(f19,conjecture,(
% 1.60/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.60/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.60/0.61  fof(f142,plain,(
% 1.60/0.61    spl10_5),
% 1.60/0.61    inference(avatar_split_clause,[],[f71,f139])).
% 1.60/0.61  fof(f71,plain,(
% 1.60/0.61    v1_funct_2(sK6,sK5,sK5)),
% 1.60/0.61    inference(cnf_transformation,[],[f57])).
% 1.60/0.61  fof(f137,plain,(
% 1.60/0.61    spl10_4),
% 1.60/0.61    inference(avatar_split_clause,[],[f72,f134])).
% 1.60/0.61  fof(f72,plain,(
% 1.60/0.61    v3_funct_2(sK6,sK5,sK5)),
% 1.60/0.61    inference(cnf_transformation,[],[f57])).
% 1.60/0.61  fof(f132,plain,(
% 1.60/0.61    spl10_3),
% 1.60/0.61    inference(avatar_split_clause,[],[f73,f129])).
% 1.60/0.61  fof(f73,plain,(
% 1.60/0.61    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))),
% 1.60/0.61    inference(cnf_transformation,[],[f57])).
% 1.60/0.61  fof(f127,plain,(
% 1.60/0.61    ~spl10_1 | ~spl10_2),
% 1.60/0.61    inference(avatar_split_clause,[],[f74,f124,f120])).
% 1.60/0.61  fof(f74,plain,(
% 1.60/0.61    ~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,k2_funct_2(sK5,sK6),sK6),k6_partfun1(sK5)) | ~r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK5,sK5,sK5,sK6,k2_funct_2(sK5,sK6)),k6_partfun1(sK5))),
% 1.60/0.61    inference(cnf_transformation,[],[f57])).
% 1.60/0.61  % SZS output end Proof for theBenchmark
% 1.60/0.61  % (7352)------------------------------
% 1.60/0.61  % (7352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.61  % (7352)Termination reason: Refutation
% 1.60/0.61  
% 1.60/0.61  % (7352)Memory used [KB]: 12792
% 1.60/0.61  % (7352)Time elapsed: 0.173 s
% 1.60/0.61  % (7352)------------------------------
% 1.60/0.61  % (7352)------------------------------
% 1.60/0.61  % (7335)Success in time 0.244 s
%------------------------------------------------------------------------------
