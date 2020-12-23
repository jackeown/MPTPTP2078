%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0864+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 5.17s
% Output     : Refutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :  332 ( 652 expanded)
%              Number of leaves         :   96 ( 265 expanded)
%              Depth                    :   11
%              Number of atoms          :  673 (1351 expanded)
%              Number of equality atoms :  160 ( 491 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2527,f2536,f2560,f2566,f2571,f2576,f2581,f2586,f2591,f2596,f2601,f2607,f2633,f2639,f2645,f2651,f2657,f2664,f2670,f2680,f2688,f2693,f2702,f2707,f2713,f2719,f2748,f2766,f2951,f2994,f3788,f4316,f4558,f4674,f4698,f4703,f4770,f4775,f4786,f4787,f4792,f4797,f4802,f4848,f4854,f4855,f4890,f4895,f4900,f4905,f4910,f4915,f4920,f4923,f4928,f4939,f4951,f5042,f5078])).

fof(f5078,plain,(
    ~ spl100_40 ),
    inference(avatar_contradiction_clause,[],[f5077])).

fof(f5077,plain,
    ( $false
    | ~ spl100_40 ),
    inference(resolution,[],[f5075,f2498])).

fof(f2498,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f2497])).

fof(f2497,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f2025])).

fof(f2025,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f5075,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k1_tarski(X0))
    | ~ spl100_40 ),
    inference(subsumption_resolution,[],[f5035,f5073])).

fof(f5073,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k1_tarski(X0))
    | ~ spl100_40 ),
    inference(subsumption_resolution,[],[f5072,f2496])).

fof(f2496,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f2026])).

fof(f2026,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f5072,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0)) )
    | ~ spl100_40 ),
    inference(subsumption_resolution,[],[f5071,f3682])).

fof(f3682,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f2043,f2203])).

fof(f2203,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f2043,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f5071,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_xboole_0 = k1_tarski(X0) )
    | ~ spl100_40 ),
    inference(superposition,[],[f4825,f4596])).

fof(f4596,plain,(
    ! [X46] : sK37(k1_tarski(X46)) = X46 ),
    inference(subsumption_resolution,[],[f4590,f3682])).

fof(f4590,plain,(
    ! [X46] :
      ( sK37(k1_tarski(X46)) = X46
      | k1_xboole_0 = k1_tarski(X46) ) ),
    inference(resolution,[],[f2496,f1842])).

fof(f1842,plain,(
    ! [X0] :
      ( r2_hidden(sK37(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1357])).

fof(f1357,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1312])).

fof(f1312,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f4825,plain,
    ( ! [X39] :
        ( sK0 != sK37(X39)
        | ~ r2_hidden(sK0,X39)
        | k1_xboole_0 = X39 )
    | ~ spl100_40 ),
    inference(superposition,[],[f1840,f4785])).

fof(f4785,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl100_40 ),
    inference(avatar_component_clause,[],[f4783])).

fof(f4783,plain,
    ( spl100_40
  <=> sK0 = k4_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_40])])).

fof(f1840,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK37(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1357])).

fof(f5035,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_tarski(k4_tarski(sK0,X0)))
        | ~ r2_hidden(sK2,k1_tarski(X0)) )
    | ~ spl100_40 ),
    inference(superposition,[],[f4833,f1836])).

fof(f1836,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f393])).

fof(f393,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f4833,plain,
    ( ! [X52] :
        ( r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK0),X52))
        | ~ r2_hidden(sK2,X52) )
    | ~ spl100_40 ),
    inference(superposition,[],[f2449,f4785])).

fof(f2449,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f1783])).

fof(f1783,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f344])).

fof(f344,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f5042,plain,
    ( ~ spl100_55
    | ~ spl100_40
    | spl100_43 ),
    inference(avatar_split_clause,[],[f5037,f4799,f4783,f5039])).

fof(f5039,plain,
    ( spl100_55
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_55])])).

fof(f4799,plain,
    ( spl100_43
  <=> r2_hidden(sK26(sK0,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_43])])).

fof(f5037,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl100_40
    | spl100_43 ),
    inference(subsumption_resolution,[],[f5027,f4801])).

fof(f4801,plain,
    ( ~ r2_hidden(sK26(sK0,k1_tarski(sK0)),k1_tarski(sK0))
    | spl100_43 ),
    inference(avatar_component_clause,[],[f4799])).

fof(f5027,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r2_hidden(sK26(sK0,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl100_40 ),
    inference(resolution,[],[f4833,f1818])).

fof(f1818,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X0))
      | r2_hidden(sK26(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1354])).

fof(f1354,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(X2,k1_tarski(X2)) = X0
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(ennf_transformation,[],[f371])).

fof(f371,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( k4_tarski(X2,k1_tarski(X2)) = X0
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_zfmisc_1)).

fof(f4951,plain,
    ( ~ spl100_54
    | spl100_53 ),
    inference(avatar_split_clause,[],[f4946,f4936,f4948])).

fof(f4948,plain,
    ( spl100_54
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_54])])).

fof(f4936,plain,
    ( spl100_53
  <=> r2_hidden(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_53])])).

fof(f4946,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl100_53 ),
    inference(resolution,[],[f4938,f2509])).

fof(f2509,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f2140])).

fof(f2140,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f4938,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK2))
    | spl100_53 ),
    inference(avatar_component_clause,[],[f4936])).

fof(f4939,plain,
    ( ~ spl100_53
    | spl100_46 ),
    inference(avatar_split_clause,[],[f4933,f4892,f4936])).

fof(f4892,plain,
    ( spl100_46
  <=> r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_46])])).

fof(f4933,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK2))
    | spl100_46 ),
    inference(resolution,[],[f4893,f2015])).

fof(f2015,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f4893,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK2))
    | spl100_46 ),
    inference(avatar_component_clause,[],[f4892])).

fof(f4928,plain,
    ( spl100_52
    | ~ spl100_40 ),
    inference(avatar_split_clause,[],[f4843,f4783,f4925])).

fof(f4925,plain,
    ( spl100_52
  <=> k2_relat_1(k1_tarski(sK0)) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_52])])).

fof(f4843,plain,
    ( k2_relat_1(k1_tarski(sK0)) = k1_tarski(sK2)
    | ~ spl100_40 ),
    inference(superposition,[],[f2548,f4785])).

fof(f2548,plain,(
    ! [X0,X1] : k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f2456,f1837])).

fof(f1837,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f695])).

fof(f695,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).

fof(f2456,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f1813])).

fof(f1813,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | k1_tarski(X1) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1351])).

fof(f1351,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1350])).

fof(f1350,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f827])).

fof(f827,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f4923,plain,
    ( spl100_19
    | ~ spl100_44 ),
    inference(avatar_contradiction_clause,[],[f4922])).

fof(f4922,plain,
    ( $false
    | spl100_19
    | ~ spl100_44 ),
    inference(subsumption_resolution,[],[f4921,f2662])).

fof(f2662,plain,
    ( sK0 != sK2
    | spl100_19 ),
    inference(avatar_component_clause,[],[f2661])).

fof(f2661,plain,
    ( spl100_19
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_19])])).

fof(f4921,plain,
    ( sK0 = sK2
    | ~ spl100_44 ),
    inference(forward_demodulation,[],[f4883,f4596])).

fof(f4883,plain,
    ( sK2 = sK37(k1_tarski(sK0))
    | ~ spl100_44 ),
    inference(superposition,[],[f4596,f4853])).

fof(f4853,plain,
    ( k1_tarski(sK0) = k1_tarski(sK2)
    | ~ spl100_44 ),
    inference(avatar_component_clause,[],[f4851])).

fof(f4851,plain,
    ( spl100_44
  <=> k1_tarski(sK0) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_44])])).

fof(f4920,plain,
    ( spl100_51
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4882,f4851,f4917])).

fof(f4917,plain,
    ( spl100_51
  <=> m1_subset_1(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_51])])).

fof(f4882,plain,
    ( m1_subset_1(sK2,k1_tarski(sK0))
    | ~ spl100_44 ),
    inference(superposition,[],[f3948,f4853])).

fof(f3948,plain,(
    ! [X0] : m1_subset_1(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f2136,f2498])).

fof(f2136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1513])).

fof(f1513,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f4915,plain,
    ( ~ spl100_50
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4880,f4851,f4912])).

fof(f4912,plain,
    ( spl100_50
  <=> r2_hidden(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_50])])).

fof(f4880,plain,
    ( ~ r2_hidden(k1_tarski(sK0),sK2)
    | ~ spl100_44 ),
    inference(superposition,[],[f3275,f4853])).

fof(f3275,plain,(
    ! [X0] : ~ r2_hidden(k1_tarski(X0),X0) ),
    inference(resolution,[],[f1883,f2498])).

fof(f1883,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1375])).

fof(f1375,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f4910,plain,
    ( ~ spl100_49
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4879,f4851,f4907])).

fof(f4907,plain,
    ( spl100_49
  <=> r2_hidden(k1_zfmisc_1(sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_49])])).

fof(f4879,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_tarski(sK0))
    | ~ spl100_44 ),
    inference(superposition,[],[f3214,f4853])).

fof(f3214,plain,(
    ! [X10] : ~ r2_hidden(k1_zfmisc_1(X10),k1_tarski(X10)) ),
    inference(resolution,[],[f1877,f2045])).

fof(f2045,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f1877,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1372])).

fof(f1372,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f4905,plain,
    ( spl100_48
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4878,f4851,f4902])).

fof(f4902,plain,
    ( spl100_48
  <=> r2_hidden(k1_tarski(sK0),k4_tarski(sK2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_48])])).

fof(f4878,plain,
    ( r2_hidden(k1_tarski(sK0),k4_tarski(sK2,k1_tarski(sK0)))
    | ~ spl100_44 ),
    inference(superposition,[],[f3129,f4853])).

fof(f3129,plain,(
    ! [X1] : r2_hidden(k1_tarski(X1),k4_tarski(X1,k1_tarski(X1))) ),
    inference(resolution,[],[f1870,f1788])).

fof(f1788,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1870,plain,(
    ! [X0] : r2_hidden(k4_tarski(X0,k1_tarski(X0)),k2_zfmisc_1(k1_tarski(X0),k4_tarski(X0,k1_tarski(X0)))) ),
    inference(cnf_transformation,[],[f370])).

fof(f370,axiom,(
    ! [X0] : r2_hidden(k4_tarski(X0,k1_tarski(X0)),k2_zfmisc_1(k1_tarski(X0),k4_tarski(X0,k1_tarski(X0)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_zfmisc_1)).

fof(f4900,plain,
    ( spl100_47
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4876,f4851,f4897])).

fof(f4897,plain,
    ( spl100_47
  <=> r2_hidden(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_47])])).

fof(f4876,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl100_44 ),
    inference(superposition,[],[f2498,f4853])).

fof(f4895,plain,
    ( spl100_46
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4869,f4851,f4892])).

fof(f4869,plain,
    ( r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK2))
    | ~ spl100_44 ),
    inference(superposition,[],[f2045,f4853])).

fof(f4890,plain,
    ( spl100_45
    | ~ spl100_44 ),
    inference(avatar_split_clause,[],[f4865,f4851,f4887])).

fof(f4887,plain,
    ( spl100_45
  <=> r2_hidden(k4_tarski(sK2,k1_tarski(sK0)),k2_zfmisc_1(k1_tarski(sK0),k4_tarski(sK2,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_45])])).

fof(f4865,plain,
    ( r2_hidden(k4_tarski(sK2,k1_tarski(sK0)),k2_zfmisc_1(k1_tarski(sK0),k4_tarski(sK2,k1_tarski(sK0))))
    | ~ spl100_44 ),
    inference(superposition,[],[f1870,f4853])).

fof(f4855,plain,
    ( spl100_42
    | ~ spl100_40 ),
    inference(avatar_split_clause,[],[f4842,f4783,f4794])).

fof(f4794,plain,
    ( spl100_42
  <=> k1_tarski(sK0) = k1_relat_1(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_42])])).

fof(f4842,plain,
    ( k1_tarski(sK0) = k1_relat_1(k1_tarski(sK0))
    | ~ spl100_40 ),
    inference(superposition,[],[f2547,f4785])).

fof(f2547,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f2457,f1837])).

fof(f2457,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f1812])).

fof(f1812,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | k1_tarski(X0) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1351])).

fof(f4854,plain,
    ( spl100_44
    | ~ spl100_27
    | ~ spl100_40 ),
    inference(avatar_split_clause,[],[f4849,f4783,f2716,f4851])).

fof(f2716,plain,
    ( spl100_27
  <=> k1_tarski(sK0) = k2_relat_1(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_27])])).

fof(f4849,plain,
    ( k1_tarski(sK0) = k1_tarski(sK2)
    | ~ spl100_27
    | ~ spl100_40 ),
    inference(forward_demodulation,[],[f4843,f2718])).

fof(f2718,plain,
    ( k1_tarski(sK0) = k2_relat_1(k1_tarski(sK0))
    | ~ spl100_27 ),
    inference(avatar_component_clause,[],[f2716])).

fof(f4848,plain,
    ( ~ spl100_40
    | spl100_42 ),
    inference(avatar_contradiction_clause,[],[f4847])).

fof(f4847,plain,
    ( $false
    | ~ spl100_40
    | spl100_42 ),
    inference(subsumption_resolution,[],[f4842,f4795])).

fof(f4795,plain,
    ( k1_tarski(sK0) != k1_relat_1(k1_tarski(sK0))
    | spl100_42 ),
    inference(avatar_component_clause,[],[f4794])).

fof(f4802,plain,
    ( ~ spl100_43
    | ~ spl100_18
    | spl100_31 ),
    inference(avatar_split_clause,[],[f4781,f2987,f2654,f4799])).

fof(f2654,plain,
    ( spl100_18
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_18])])).

fof(f2987,plain,
    ( spl100_31
  <=> r2_hidden(sK26(sK0,k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_31])])).

fof(f4781,plain,
    ( ~ r2_hidden(sK26(sK0,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl100_18
    | spl100_31 ),
    inference(backward_demodulation,[],[f2988,f2655])).

fof(f2655,plain,
    ( sK0 = sK1
    | ~ spl100_18 ),
    inference(avatar_component_clause,[],[f2654])).

fof(f2988,plain,
    ( ~ r2_hidden(sK26(sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | spl100_31 ),
    inference(avatar_component_clause,[],[f2987])).

fof(f4797,plain,
    ( spl100_42
    | ~ spl100_18
    | ~ spl100_26 ),
    inference(avatar_split_clause,[],[f4779,f2710,f2654,f4794])).

fof(f2710,plain,
    ( spl100_26
  <=> k1_tarski(sK1) = k1_relat_1(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_26])])).

fof(f4779,plain,
    ( k1_tarski(sK0) = k1_relat_1(k1_tarski(sK0))
    | ~ spl100_18
    | ~ spl100_26 ),
    inference(backward_demodulation,[],[f2712,f2655])).

fof(f2712,plain,
    ( k1_tarski(sK1) = k1_relat_1(k1_tarski(sK0))
    | ~ spl100_26 ),
    inference(avatar_component_clause,[],[f2710])).

fof(f4792,plain,
    ( ~ spl100_41
    | ~ spl100_18
    | spl100_20 ),
    inference(avatar_split_clause,[],[f4778,f2667,f2654,f4789])).

fof(f4789,plain,
    ( spl100_41
  <=> sK0 = k4_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_41])])).

fof(f2667,plain,
    ( spl100_20
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_20])])).

fof(f4778,plain,
    ( sK0 != k4_tarski(sK0,sK0)
    | ~ spl100_18
    | spl100_20 ),
    inference(backward_demodulation,[],[f2668,f2655])).

fof(f2668,plain,
    ( sK0 != k4_tarski(sK1,sK0)
    | spl100_20 ),
    inference(avatar_component_clause,[],[f2667])).

fof(f4787,plain,
    ( spl100_3
    | ~ spl100_17
    | ~ spl100_18 ),
    inference(avatar_split_clause,[],[f4777,f2654,f2648,f2533])).

fof(f2533,plain,
    ( spl100_3
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_3])])).

fof(f2648,plain,
    ( spl100_17
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_17])])).

fof(f4777,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl100_17
    | ~ spl100_18 ),
    inference(backward_demodulation,[],[f2650,f2655])).

fof(f2650,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl100_17 ),
    inference(avatar_component_clause,[],[f2648])).

fof(f4786,plain,
    ( spl100_40
    | ~ spl100_1
    | ~ spl100_18 ),
    inference(avatar_split_clause,[],[f4776,f2654,f2524,f4783])).

fof(f2524,plain,
    ( spl100_1
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_1])])).

fof(f4776,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl100_1
    | ~ spl100_18 ),
    inference(backward_demodulation,[],[f2526,f2655])).

fof(f2526,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl100_1 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f4775,plain,
    ( spl100_39
    | ~ spl100_1 ),
    inference(avatar_split_clause,[],[f2658,f2524,f4772])).

fof(f4772,plain,
    ( spl100_39
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_39])])).

fof(f2658,plain,
    ( sK2 = k2_mcart_1(sK0)
    | ~ spl100_1 ),
    inference(superposition,[],[f1757,f2526])).

fof(f1757,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1310])).

fof(f1310,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f4770,plain,(
    ~ spl100_20 ),
    inference(avatar_contradiction_clause,[],[f4769])).

fof(f4769,plain,
    ( $false
    | ~ spl100_20 ),
    inference(resolution,[],[f4719,f2498])).

fof(f4719,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k1_tarski(X0))
    | ~ spl100_20 ),
    inference(subsumption_resolution,[],[f3065,f4715])).

fof(f4715,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k1_tarski(X0))
    | ~ spl100_20 ),
    inference(subsumption_resolution,[],[f4714,f2496])).

fof(f4714,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0)) )
    | ~ spl100_20 ),
    inference(subsumption_resolution,[],[f4709,f3682])).

fof(f4709,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_xboole_0 = k1_tarski(X0) )
    | ~ spl100_20 ),
    inference(superposition,[],[f3073,f4596])).

fof(f3073,plain,
    ( ! [X0] :
        ( sK0 != sK37(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl100_20 ),
    inference(superposition,[],[f1841,f2669])).

fof(f2669,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl100_20 ),
    inference(avatar_component_clause,[],[f2667])).

fof(f1841,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK37(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1357])).

fof(f3065,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_tarski(k4_tarski(X0,sK0)))
        | ~ r2_hidden(sK1,k1_tarski(X0)) )
    | ~ spl100_20 ),
    inference(superposition,[],[f2940,f1836])).

fof(f2940,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,k1_tarski(sK0)))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl100_20 ),
    inference(superposition,[],[f2450,f2669])).

fof(f2450,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f1786])).

fof(f1786,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f345])).

fof(f345,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f4703,plain,
    ( spl100_38
    | ~ spl100_4 ),
    inference(avatar_split_clause,[],[f4692,f2557,f4700])).

fof(f4700,plain,
    ( spl100_38
  <=> r1_tarski(sK76(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_38])])).

fof(f2557,plain,
    ( spl100_4
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_4])])).

fof(f4692,plain,
    ( r1_tarski(sK76(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl100_4 ),
    inference(superposition,[],[f4549,f2559])).

fof(f2559,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl100_4 ),
    inference(avatar_component_clause,[],[f2557])).

fof(f4549,plain,(
    ! [X17] : r1_tarski(sK76(k1_zfmisc_1(X17)),X17) ),
    inference(resolution,[],[f2121,f2137])).

fof(f2137,plain,(
    ! [X0] : m1_subset_1(sK76(X0),X0) ),
    inference(cnf_transformation,[],[f474])).

fof(f474,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f2121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f4698,plain,
    ( spl100_37
    | ~ spl100_4 ),
    inference(avatar_split_clause,[],[f4693,f2557,f4695])).

fof(f4695,plain,
    ( spl100_37
  <=> k1_xboole_0 = sK76(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_37])])).

fof(f4693,plain,
    ( k1_xboole_0 = sK76(k1_tarski(k1_xboole_0))
    | ~ spl100_4 ),
    inference(forward_demodulation,[],[f4691,f2559])).

fof(f4691,plain,(
    k1_xboole_0 = sK76(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f4549,f2202])).

fof(f2202,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1561])).

fof(f1561,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f4674,plain,
    ( ~ spl100_36
    | ~ spl100_4 ),
    inference(avatar_split_clause,[],[f4669,f2557,f4671])).

fof(f4671,plain,
    ( spl100_36
  <=> r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_36])])).

fof(f4669,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl100_4 ),
    inference(superposition,[],[f4636,f2559])).

fof(f4636,plain,(
    ! [X2] : ~ r1_tarski(k1_zfmisc_1(X2),X2) ),
    inference(resolution,[],[f2509,f3208])).

fof(f3208,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f1877,f2499])).

fof(f2499,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2049])).

fof(f2049,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4558,plain,(
    spl100_35 ),
    inference(avatar_split_clause,[],[f4553,f4555])).

fof(f4555,plain,
    ( spl100_35
  <=> k1_xboole_0 = sK83(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_35])])).

fof(f4553,plain,(
    k1_xboole_0 = sK83(k1_xboole_0) ),
    inference(resolution,[],[f4550,f2202])).

fof(f4550,plain,(
    ! [X18] : r1_tarski(sK83(X18),X18) ),
    inference(resolution,[],[f2121,f2180])).

fof(f2180,plain,(
    ! [X0] : m1_subset_1(sK83(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f490])).

fof(f490,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f4316,plain,(
    spl100_34 ),
    inference(avatar_split_clause,[],[f4310,f4313])).

fof(f4313,plain,
    ( spl100_34
  <=> k1_xboole_0 = k2_relat_1(sK65(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_34])])).

fof(f4310,plain,(
    k1_xboole_0 = k2_relat_1(sK65(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f2504,f2202])).

fof(f2504,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK65(X0,k1_xboole_0)),X0) ),
    inference(equality_resolution,[],[f2087])).

fof(f2087,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | r1_tarski(k2_relat_1(sK65(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f1477])).

fof(f1477,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1476])).

fof(f1476,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1001])).

fof(f1001,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f3788,plain,
    ( spl100_33
    | ~ spl100_4 ),
    inference(avatar_split_clause,[],[f3783,f2557,f3785])).

fof(f3785,plain,
    ( spl100_33
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_33])])).

fof(f3783,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl100_4 ),
    inference(superposition,[],[f2044,f2559])).

fof(f2044,plain,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f631])).

fof(f631,axiom,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f2994,plain,
    ( spl100_31
    | ~ spl100_32
    | ~ spl100_20 ),
    inference(avatar_split_clause,[],[f2979,f2667,f2991,f2987])).

fof(f2991,plain,
    ( spl100_32
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_32])])).

fof(f2979,plain,
    ( ~ r2_hidden(sK0,sK0)
    | r2_hidden(sK26(sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl100_20 ),
    inference(resolution,[],[f2920,f1818])).

fof(f2920,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),X0))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl100_20 ),
    inference(superposition,[],[f2449,f2669])).

fof(f2951,plain,
    ( ~ spl100_30
    | ~ spl100_20 ),
    inference(avatar_split_clause,[],[f2946,f2667,f2948])).

fof(f2948,plain,
    ( spl100_30
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_30])])).

fof(f2946,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl100_20 ),
    inference(superposition,[],[f2934,f2669])).

fof(f2934,plain,(
    ! [X17,X16] : ~ r2_hidden(X16,k4_tarski(X16,X17)) ),
    inference(resolution,[],[f2450,f1924])).

fof(f1924,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f2766,plain,
    ( spl100_29
    | ~ spl100_4 ),
    inference(avatar_split_clause,[],[f2761,f2557,f2763])).

fof(f2763,plain,
    ( spl100_29
  <=> m1_subset_1(sK83(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_29])])).

fof(f2761,plain,
    ( m1_subset_1(sK83(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl100_4 ),
    inference(superposition,[],[f2180,f2559])).

fof(f2748,plain,
    ( spl100_28
    | ~ spl100_4 ),
    inference(avatar_split_clause,[],[f2742,f2557,f2745])).

fof(f2745,plain,
    ( spl100_28
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_28])])).

fof(f2742,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl100_4 ),
    inference(superposition,[],[f2148,f2559])).

fof(f2148,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2719,plain,
    ( spl100_27
    | ~ spl100_20 ),
    inference(avatar_split_clause,[],[f2714,f2667,f2716])).

fof(f2714,plain,
    ( k1_tarski(sK0) = k2_relat_1(k1_tarski(sK0))
    | ~ spl100_20 ),
    inference(superposition,[],[f2548,f2669])).

fof(f2713,plain,
    ( spl100_26
    | ~ spl100_20 ),
    inference(avatar_split_clause,[],[f2708,f2667,f2710])).

fof(f2708,plain,
    ( k1_tarski(sK1) = k1_relat_1(k1_tarski(sK0))
    | ~ spl100_20 ),
    inference(superposition,[],[f2547,f2669])).

fof(f2707,plain,
    ( spl100_25
    | ~ spl100_13 ),
    inference(avatar_split_clause,[],[f2696,f2604,f2704])).

fof(f2704,plain,
    ( spl100_25
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_25])])).

fof(f2604,plain,
    ( spl100_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_13])])).

fof(f2696,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl100_13 ),
    inference(resolution,[],[f2192,f2606])).

fof(f2606,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl100_13 ),
    inference(avatar_component_clause,[],[f2604])).

fof(f2192,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f1556])).

fof(f1556,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f2702,plain,
    ( spl100_24
    | ~ spl100_11 ),
    inference(avatar_split_clause,[],[f2695,f2593,f2699])).

fof(f2699,plain,
    ( spl100_24
  <=> v1_funct_1(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_24])])).

fof(f2593,plain,
    ( spl100_11
  <=> v1_xboole_0(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_11])])).

fof(f2695,plain,
    ( v1_funct_1(sK81)
    | ~ spl100_11 ),
    inference(resolution,[],[f2192,f2595])).

fof(f2595,plain,
    ( v1_xboole_0(sK81)
    | ~ spl100_11 ),
    inference(avatar_component_clause,[],[f2593])).

fof(f2693,plain,
    ( spl100_23
    | ~ spl100_13 ),
    inference(avatar_split_clause,[],[f2682,f2604,f2690])).

fof(f2690,plain,
    ( spl100_23
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_23])])).

fof(f2682,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl100_13 ),
    inference(resolution,[],[f2191,f2606])).

fof(f2191,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1555])).

fof(f1555,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f2688,plain,
    ( spl100_22
    | ~ spl100_11 ),
    inference(avatar_split_clause,[],[f2681,f2593,f2685])).

fof(f2685,plain,
    ( spl100_22
  <=> v1_relat_1(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_22])])).

fof(f2681,plain,
    ( v1_relat_1(sK81)
    | ~ spl100_11 ),
    inference(resolution,[],[f2191,f2595])).

fof(f2680,plain,
    ( ~ spl100_21
    | ~ spl100_20 ),
    inference(avatar_split_clause,[],[f2675,f2667,f2677])).

fof(f2677,plain,
    ( spl100_21
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_21])])).

fof(f2675,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl100_20 ),
    inference(superposition,[],[f1839,f2669])).

fof(f1839,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f292])).

fof(f292,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(f2670,plain,
    ( spl100_20
    | ~ spl100_1
    | ~ spl100_19 ),
    inference(avatar_split_clause,[],[f2665,f2661,f2524,f2667])).

fof(f2665,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl100_1
    | ~ spl100_19 ),
    inference(backward_demodulation,[],[f2526,f2663])).

fof(f2663,plain,
    ( sK0 = sK2
    | ~ spl100_19 ),
    inference(avatar_component_clause,[],[f2661])).

fof(f2664,plain,
    ( spl100_19
    | ~ spl100_1
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2659,f2529,f2524,f2661])).

fof(f2529,plain,
    ( spl100_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_2])])).

fof(f2659,plain,
    ( sK0 = sK2
    | ~ spl100_1
    | ~ spl100_2 ),
    inference(forward_demodulation,[],[f2658,f2531])).

fof(f2531,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl100_2 ),
    inference(avatar_component_clause,[],[f2529])).

fof(f2657,plain,
    ( ~ spl100_18
    | spl100_3
    | ~ spl100_17 ),
    inference(avatar_split_clause,[],[f2652,f2648,f2533,f2654])).

fof(f2652,plain,
    ( sK0 != sK1
    | spl100_3
    | ~ spl100_17 ),
    inference(superposition,[],[f2534,f2650])).

fof(f2534,plain,
    ( sK0 != k1_mcart_1(sK0)
    | spl100_3 ),
    inference(avatar_component_clause,[],[f2533])).

fof(f2651,plain,
    ( spl100_17
    | ~ spl100_1 ),
    inference(avatar_split_clause,[],[f2646,f2524,f2648])).

fof(f2646,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl100_1 ),
    inference(superposition,[],[f1756,f2526])).

fof(f1756,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1310])).

fof(f2645,plain,
    ( spl100_16
    | ~ spl100_1 ),
    inference(avatar_split_clause,[],[f2640,f2524,f2642])).

fof(f2642,plain,
    ( spl100_16
  <=> v1_funct_1(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_16])])).

fof(f2640,plain,
    ( v1_funct_1(k1_tarski(sK0))
    | ~ spl100_1 ),
    inference(superposition,[],[f1838,f2526])).

fof(f1838,plain,(
    ! [X0,X1] : v1_funct_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f916])).

fof(f916,axiom,(
    ! [X0,X1] : v1_funct_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_funct_1)).

fof(f2639,plain,
    ( spl100_15
    | ~ spl100_1 ),
    inference(avatar_split_clause,[],[f2634,f2524,f2636])).

fof(f2636,plain,
    ( spl100_15
  <=> v1_relat_1(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_15])])).

fof(f2634,plain,
    ( v1_relat_1(k1_tarski(sK0))
    | ~ spl100_1 ),
    inference(superposition,[],[f1837,f2526])).

fof(f2633,plain,(
    spl100_14 ),
    inference(avatar_split_clause,[],[f2520,f2630])).

fof(f2630,plain,
    ( spl100_14
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_14])])).

fof(f2520,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2433])).

fof(f2433,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1734])).

fof(f1734,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f2607,plain,(
    spl100_13 ),
    inference(avatar_split_clause,[],[f2199,f2604])).

fof(f2199,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2601,plain,(
    ~ spl100_12 ),
    inference(avatar_split_clause,[],[f2154,f2598])).

fof(f2598,plain,
    ( spl100_12
  <=> v1_xboole_0(sK82) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_12])])).

fof(f2154,plain,(
    ~ v1_xboole_0(sK82) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_xboole_0)).

fof(f2596,plain,(
    spl100_11 ),
    inference(avatar_split_clause,[],[f2153,f2593])).

fof(f2153,plain,(
    v1_xboole_0(sK81) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f2591,plain,(
    ~ spl100_10 ),
    inference(avatar_split_clause,[],[f2151,f2588])).

fof(f2588,plain,
    ( spl100_10
  <=> v1_xboole_0(sK80) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_10])])).

fof(f2151,plain,(
    ~ v1_xboole_0(sK80) ),
    inference(cnf_transformation,[],[f702])).

fof(f702,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f2586,plain,(
    spl100_9 ),
    inference(avatar_split_clause,[],[f2152,f2583])).

fof(f2583,plain,
    ( spl100_9
  <=> v1_relat_1(sK80) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_9])])).

fof(f2152,plain,(
    v1_relat_1(sK80) ),
    inference(cnf_transformation,[],[f702])).

fof(f2581,plain,(
    spl100_8 ),
    inference(avatar_split_clause,[],[f2149,f2578])).

fof(f2578,plain,
    ( spl100_8
  <=> v1_relat_1(sK79) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_8])])).

fof(f2149,plain,(
    v1_relat_1(sK79) ),
    inference(cnf_transformation,[],[f930])).

fof(f930,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f2576,plain,(
    spl100_7 ),
    inference(avatar_split_clause,[],[f2150,f2573])).

fof(f2573,plain,
    ( spl100_7
  <=> v1_funct_1(sK79) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_7])])).

fof(f2150,plain,(
    v1_funct_1(sK79) ),
    inference(cnf_transformation,[],[f930])).

fof(f2571,plain,(
    spl100_6 ),
    inference(avatar_split_clause,[],[f2108,f2568])).

fof(f2568,plain,
    ( spl100_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_6])])).

fof(f2108,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f2566,plain,(
    spl100_5 ),
    inference(avatar_split_clause,[],[f2109,f2563])).

fof(f2563,plain,
    ( spl100_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_5])])).

fof(f2109,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f2560,plain,(
    spl100_4 ),
    inference(avatar_split_clause,[],[f2046,f2557])).

fof(f2046,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f2536,plain,
    ( spl100_2
    | spl100_3 ),
    inference(avatar_split_clause,[],[f1735,f2533,f2529])).

fof(f1735,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1320])).

fof(f1320,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f1304])).

fof(f1304,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f1303])).

fof(f1303,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f2527,plain,(
    spl100_1 ),
    inference(avatar_split_clause,[],[f1736,f2524])).

fof(f1736,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f1320])).
%------------------------------------------------------------------------------
