%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 361 expanded)
%              Number of leaves         :   45 ( 162 expanded)
%              Depth                    :   11
%              Number of atoms          :  569 (1122 expanded)
%              Number of equality atoms :   55 ( 119 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1737,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f189,f200,f215,f220,f231,f267,f283,f299,f338,f365,f513,f518,f597,f628,f663,f668,f677,f919,f971,f1071,f1077,f1105,f1119,f1416,f1723,f1729])).

fof(f1729,plain,
    ( ~ spl4_7
    | ~ spl4_11
    | ~ spl4_57
    | ~ spl4_127 ),
    inference(avatar_contradiction_clause,[],[f1724])).

fof(f1724,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_57
    | ~ spl4_127 ),
    inference(unit_resulting_resolution,[],[f84,f50,f141,f1722,f596])).

fof(f596,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl4_57
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1722,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f1720])).

fof(f1720,plain,
    ( spl4_127
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f141,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_11
  <=> r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f50,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f84,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1723,plain,
    ( spl4_5
    | ~ spl4_7
    | ~ spl4_1
    | ~ spl4_4
    | spl4_127
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f1718,f133,f1720,f67,f52,f82,f72])).

fof(f72,plain,
    ( spl4_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f52,plain,
    ( spl4_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( spl4_4
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f133,plain,
    ( spl4_10
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1718,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(superposition,[],[f35,f135])).

fof(f135,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f1416,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f1415,f133,f77,f139])).

fof(f77,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1415,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f79,f135])).

fof(f79,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f1119,plain,
    ( k1_xboole_0 != k1_orders_2(sK0,k1_xboole_0)
    | k1_xboole_0 != k6_domain_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != sK1
    | k1_tarski(k1_xboole_0) != k6_domain_1(k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1105,plain,
    ( spl4_98
    | spl4_59
    | ~ spl4_91 ),
    inference(avatar_split_clause,[],[f1094,f981,f625,f1102])).

fof(f1102,plain,
    ( spl4_98
  <=> k1_xboole_0 = k1_orders_2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f625,plain,
    ( spl4_59
  <=> v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f981,plain,
    ( spl4_91
  <=> m1_subset_1(k1_orders_2(sK0,k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1094,plain,
    ( k1_xboole_0 = k1_orders_2(sK0,k1_xboole_0)
    | spl4_59
    | ~ spl4_91 ),
    inference(resolution,[],[f982,f651])).

fof(f651,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | spl4_59 ),
    inference(resolution,[],[f627,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tarski(X0))
      | ~ m1_subset_1(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f627,plain,
    ( ~ v1_xboole_0(k1_tarski(k1_xboole_0))
    | spl4_59 ),
    inference(avatar_component_clause,[],[f625])).

fof(f982,plain,
    ( m1_subset_1(k1_orders_2(sK0,k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl4_91 ),
    inference(avatar_component_clause,[],[f981])).

fof(f1077,plain,
    ( ~ spl4_37
    | spl4_79
    | ~ spl4_62
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f1024,f916,f666,f824,f362])).

fof(f362,plain,
    ( spl4_37
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f824,plain,
    ( spl4_79
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f666,plain,
    ( spl4_62
  <=> ! [X1] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f916,plain,
    ( spl4_84
  <=> k1_xboole_0 = k6_domain_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1024,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_62
    | ~ spl4_84 ),
    inference(superposition,[],[f667,f918])).

fof(f918,plain,
    ( k1_xboole_0 = k6_domain_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f916])).

fof(f667,plain,
    ( ! [X1] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_xboole_0) )
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f666])).

fof(f1071,plain,
    ( ~ spl4_79
    | ~ spl4_61
    | spl4_91 ),
    inference(avatar_split_clause,[],[f1060,f981,f661,f824])).

fof(f661,plain,
    ( spl4_61
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1060,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_61
    | spl4_91 ),
    inference(resolution,[],[f662,f983])).

fof(f983,plain,
    ( ~ m1_subset_1(k1_orders_2(sK0,k1_xboole_0),k1_tarski(k1_xboole_0))
    | spl4_91 ),
    inference(avatar_component_clause,[],[f981])).

fof(f662,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_tarski(k1_xboole_0)) )
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f661])).

fof(f971,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_zfmisc_1(u1_struct_0(sK0))
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)
    | m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f919,plain,
    ( spl4_84
    | ~ spl4_37
    | spl4_59
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f910,f666,f625,f362,f916])).

fof(f910,plain,
    ( k1_xboole_0 = k6_domain_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_37
    | spl4_59
    | ~ spl4_62 ),
    inference(resolution,[],[f702,f364])).

fof(f364,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f362])).

fof(f702,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | k1_xboole_0 = k6_domain_1(k1_xboole_0,X2) )
    | spl4_59
    | ~ spl4_62 ),
    inference(resolution,[],[f667,f651])).

fof(f677,plain,
    ( spl4_63
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f672,f335,f674])).

fof(f674,plain,
    ( spl4_63
  <=> k1_tarski(k1_xboole_0) = k6_domain_1(k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f335,plain,
    ( spl4_32
  <=> r2_hidden(k1_xboole_0,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f672,plain,
    ( k1_tarski(k1_xboole_0) = k6_domain_1(k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl4_32 ),
    inference(resolution,[],[f337,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k6_domain_1(X1,X0) ) ),
    inference(condensation,[],[f147])).

fof(f147,plain,(
    ! [X17,X18,X16] :
      ( k1_tarski(X16) = k6_domain_1(X17,X16)
      | ~ r2_hidden(X16,X17)
      | ~ r2_hidden(X18,X17) ) ),
    inference(resolution,[],[f128,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | k1_tarski(X0) = k6_domain_1(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f126])).

fof(f126,plain,(
    ! [X2,X3,X1] :
      ( k1_tarski(X1) = k6_domain_1(X2,X1)
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X1,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f108,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,X8)
      | k1_tarski(X7) = k6_domain_1(X8,X7)
      | ~ r2_hidden(X9,X8) ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f337,plain,
    ( r2_hidden(k1_xboole_0,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f335])).

fof(f668,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_4
    | spl4_62
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f664,f197,f87,f666,f67,f52,f72])).

fof(f87,plain,
    ( spl4_8
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f197,plain,
    ( spl4_16
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f664,plain,
    ( ! [X1] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_tarski(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f657,f89])).

fof(f89,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f657,plain,
    ( ! [X1] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_16 ),
    inference(superposition,[],[f35,f199])).

fof(f199,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f663,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_61
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f659,f197,f87,f661,f67,f62,f57,f52,f72])).

fof(f57,plain,
    ( spl4_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f659,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f658,f89])).

fof(f658,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f656,f89])).

fof(f656,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_16 ),
    inference(superposition,[],[f43,f199])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f628,plain,
    ( ~ spl4_59
    | ~ spl4_8
    | ~ spl4_16
    | spl4_50 ),
    inference(avatar_split_clause,[],[f623,f498,f197,f87,f625])).

fof(f498,plain,
    ( spl4_50
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f623,plain,
    ( ~ v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl4_8
    | ~ spl4_16
    | spl4_50 ),
    inference(forward_demodulation,[],[f607,f89])).

fof(f607,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16
    | spl4_50 ),
    inference(backward_demodulation,[],[f499,f199])).

fof(f499,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f498])).

fof(f597,plain,
    ( spl4_57
    | spl4_5
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f592,f52,f67,f62,f57,f72,f595])).

fof(f592,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f34,f54])).

fof(f54,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

fof(f518,plain,
    ( spl4_51
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f504,f498,f515])).

fof(f515,plain,
    ( spl4_51
  <=> k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f504,plain,
    ( k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_50 ),
    inference(resolution,[],[f500,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f500,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f498])).

fof(f513,plain,
    ( ~ spl4_46
    | ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f50,f480,f500,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f39,f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f480,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl4_46
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f365,plain,
    ( spl4_37
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f360,f280,f217,f362])).

fof(f217,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f280,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f360,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f219,f282])).

fof(f282,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f280])).

fof(f219,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f338,plain,
    ( spl4_32
    | ~ spl4_17
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f305,f280,f212,f335])).

fof(f212,plain,
    ( spl4_17
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f305,plain,
    ( r2_hidden(k1_xboole_0,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_17
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f214,f282])).

fof(f214,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f299,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f289,f82,f133,f130])).

fof(f130,plain,
    ( spl4_9
  <=> ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f289,plain,
    ( ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f84,f108])).

fof(f283,plain,
    ( spl4_25
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f278,f255,f280])).

fof(f255,plain,
    ( spl4_23
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f278,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_23 ),
    inference(resolution,[],[f256,f33])).

fof(f256,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f255])).

fof(f267,plain,
    ( ~ spl4_18
    | ~ spl4_20
    | spl4_23 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl4_18
    | ~ spl4_20
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f230,f219,f257,f39])).

fof(f257,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f255])).

fof(f230,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl4_20
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f231,plain,
    ( spl4_20
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f206,f197,f185,f228])).

fof(f185,plain,
    ( spl4_15
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f206,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f187,f199])).

fof(f187,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f220,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f202,f197,f82,f217])).

fof(f202,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f84,f199])).

fof(f215,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f201,f197,f77,f212])).

fof(f201,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1)))
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f79,f199])).

fof(f200,plain,
    ( spl4_16
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f195,f185,f197])).

fof(f195,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f187,f33])).

fof(f189,plain,
    ( spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f179,f130,f185])).

fof(f179,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f131,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f131,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f90,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f32,f87])).

fof(f32,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f85,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f25,f82])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

fof(f80,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f77])).

fof(f26,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (6917)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (6915)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (6905)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (6917)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f1737,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f189,f200,f215,f220,f231,f267,f283,f299,f338,f365,f513,f518,f597,f628,f663,f668,f677,f919,f971,f1071,f1077,f1105,f1119,f1416,f1723,f1729])).
% 0.20/0.50  fof(f1729,plain,(
% 0.20/0.50    ~spl4_7 | ~spl4_11 | ~spl4_57 | ~spl4_127),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1724])).
% 0.20/0.50  fof(f1724,plain,(
% 0.20/0.50    $false | (~spl4_7 | ~spl4_11 | ~spl4_57 | ~spl4_127)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f84,f50,f141,f1722,f596])).
% 0.20/0.50  fof(f596,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) ) | ~spl4_57),
% 0.20/0.50    inference(avatar_component_clause,[],[f595])).
% 0.20/0.50  fof(f595,plain,(
% 0.20/0.50    spl4_57 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_orders_2(sK0,X1)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.20/0.50  fof(f1722,plain,(
% 0.20/0.50    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_127),
% 0.20/0.50    inference(avatar_component_clause,[],[f1720])).
% 0.20/0.50  fof(f1720,plain,(
% 0.20/0.50    spl4_127 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | ~spl4_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl4_11 <=> r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.20/0.50    inference(equality_resolution,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl4_7 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f1723,plain,(
% 0.20/0.50    spl4_5 | ~spl4_7 | ~spl4_1 | ~spl4_4 | spl4_127 | ~spl4_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f1718,f133,f1720,f67,f52,f82,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl4_5 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl4_1 <=> l1_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl4_4 <=> v3_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl4_10 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f1718,plain,(
% 0.20/0.50    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_10),
% 0.20/0.50    inference(superposition,[],[f35,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl4_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f133])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.20/0.50  fof(f1416,plain,(
% 0.20/0.50    spl4_11 | ~spl4_6 | ~spl4_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f1415,f133,f77,f139])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl4_6 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f1415,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | (~spl4_6 | ~spl4_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f79,f135])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f1119,plain,(
% 0.20/0.50    k1_xboole_0 != k1_orders_2(sK0,k1_xboole_0) | k1_xboole_0 != k6_domain_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != u1_struct_0(sK0) | k1_xboole_0 != sK1 | k1_tarski(k1_xboole_0) != k6_domain_1(k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f1105,plain,(
% 0.20/0.50    spl4_98 | spl4_59 | ~spl4_91),
% 0.20/0.50    inference(avatar_split_clause,[],[f1094,f981,f625,f1102])).
% 0.20/0.50  fof(f1102,plain,(
% 0.20/0.50    spl4_98 <=> k1_xboole_0 = k1_orders_2(sK0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 0.20/0.50  fof(f625,plain,(
% 0.20/0.50    spl4_59 <=> v1_xboole_0(k1_tarski(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.20/0.50  fof(f981,plain,(
% 0.20/0.50    spl4_91 <=> m1_subset_1(k1_orders_2(sK0,k1_xboole_0),k1_tarski(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 0.20/0.50  fof(f1094,plain,(
% 0.20/0.50    k1_xboole_0 = k1_orders_2(sK0,k1_xboole_0) | (spl4_59 | ~spl4_91)),
% 0.20/0.50    inference(resolution,[],[f982,f651])).
% 0.20/0.50  fof(f651,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(k1_xboole_0)) | k1_xboole_0 = X0) ) | spl4_59),
% 0.20/0.50    inference(resolution,[],[f627,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(k1_tarski(X0)) | ~m1_subset_1(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.50    inference(resolution,[],[f41,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.50  fof(f627,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_tarski(k1_xboole_0)) | spl4_59),
% 0.20/0.50    inference(avatar_component_clause,[],[f625])).
% 0.20/0.50  fof(f982,plain,(
% 0.20/0.50    m1_subset_1(k1_orders_2(sK0,k1_xboole_0),k1_tarski(k1_xboole_0)) | ~spl4_91),
% 0.20/0.50    inference(avatar_component_clause,[],[f981])).
% 0.20/0.50  fof(f1077,plain,(
% 0.20/0.50    ~spl4_37 | spl4_79 | ~spl4_62 | ~spl4_84),
% 0.20/0.50    inference(avatar_split_clause,[],[f1024,f916,f666,f824,f362])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    spl4_37 <=> m1_subset_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.50  fof(f824,plain,(
% 0.20/0.50    spl4_79 <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 0.20/0.50  fof(f666,plain,(
% 0.20/0.50    spl4_62 <=> ! [X1] : (m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.20/0.50  fof(f916,plain,(
% 0.20/0.50    spl4_84 <=> k1_xboole_0 = k6_domain_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 0.20/0.50  fof(f1024,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_xboole_0) | (~spl4_62 | ~spl4_84)),
% 0.20/0.50    inference(superposition,[],[f667,f918])).
% 0.20/0.50  fof(f918,plain,(
% 0.20/0.50    k1_xboole_0 = k6_domain_1(k1_xboole_0,k1_xboole_0) | ~spl4_84),
% 0.20/0.50    inference(avatar_component_clause,[],[f916])).
% 0.20/0.50  fof(f667,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_xboole_0)) ) | ~spl4_62),
% 0.20/0.50    inference(avatar_component_clause,[],[f666])).
% 0.20/0.50  fof(f1071,plain,(
% 0.20/0.50    ~spl4_79 | ~spl4_61 | spl4_91),
% 0.20/0.50    inference(avatar_split_clause,[],[f1060,f981,f661,f824])).
% 0.20/0.50  fof(f661,plain,(
% 0.20/0.50    spl4_61 <=> ! [X0] : (~m1_subset_1(X0,k1_tarski(k1_xboole_0)) | m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.20/0.50  fof(f1060,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | (~spl4_61 | spl4_91)),
% 0.20/0.50    inference(resolution,[],[f662,f983])).
% 0.20/0.50  fof(f983,plain,(
% 0.20/0.50    ~m1_subset_1(k1_orders_2(sK0,k1_xboole_0),k1_tarski(k1_xboole_0)) | spl4_91),
% 0.20/0.50    inference(avatar_component_clause,[],[f981])).
% 0.20/0.50  fof(f662,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)) | ~m1_subset_1(X0,k1_tarski(k1_xboole_0))) ) | ~spl4_61),
% 0.20/0.50    inference(avatar_component_clause,[],[f661])).
% 0.20/0.50  fof(f971,plain,(
% 0.20/0.50    k1_xboole_0 != sK1 | k1_xboole_0 != k1_zfmisc_1(u1_struct_0(sK0)) | k1_xboole_0 != u1_struct_0(sK0) | k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) | m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f919,plain,(
% 0.20/0.50    spl4_84 | ~spl4_37 | spl4_59 | ~spl4_62),
% 0.20/0.50    inference(avatar_split_clause,[],[f910,f666,f625,f362,f916])).
% 0.20/0.50  fof(f910,plain,(
% 0.20/0.50    k1_xboole_0 = k6_domain_1(k1_xboole_0,k1_xboole_0) | (~spl4_37 | spl4_59 | ~spl4_62)),
% 0.20/0.50    inference(resolution,[],[f702,f364])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_xboole_0) | ~spl4_37),
% 0.20/0.50    inference(avatar_component_clause,[],[f362])).
% 0.20/0.50  fof(f702,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_xboole_0) | k1_xboole_0 = k6_domain_1(k1_xboole_0,X2)) ) | (spl4_59 | ~spl4_62)),
% 0.20/0.50    inference(resolution,[],[f667,f651])).
% 0.20/0.50  fof(f677,plain,(
% 0.20/0.50    spl4_63 | ~spl4_32),
% 0.20/0.50    inference(avatar_split_clause,[],[f672,f335,f674])).
% 0.20/0.50  fof(f674,plain,(
% 0.20/0.50    spl4_63 <=> k1_tarski(k1_xboole_0) = k6_domain_1(k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    spl4_32 <=> r2_hidden(k1_xboole_0,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.50  fof(f672,plain,(
% 0.20/0.50    k1_tarski(k1_xboole_0) = k6_domain_1(k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl4_32),
% 0.20/0.50    inference(resolution,[],[f337,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k6_domain_1(X1,X0)) )),
% 0.20/0.50    inference(condensation,[],[f147])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ( ! [X17,X18,X16] : (k1_tarski(X16) = k6_domain_1(X17,X16) | ~r2_hidden(X16,X17) | ~r2_hidden(X18,X17)) )),
% 0.20/0.50    inference(resolution,[],[f128,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | k1_tarski(X0) = k6_domain_1(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(condensation,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X2,X3,X1] : (k1_tarski(X1) = k6_domain_1(X2,X1) | ~r2_hidden(X3,X2) | ~r2_hidden(X1,X2) | v1_xboole_0(X2)) )),
% 0.20/0.50    inference(resolution,[],[f108,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X8,X7,X9] : (~m1_subset_1(X7,X8) | k1_tarski(X7) = k6_domain_1(X8,X7) | ~r2_hidden(X9,X8)) )),
% 0.20/0.50    inference(resolution,[],[f42,f37])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.50  fof(f337,plain,(
% 0.20/0.50    r2_hidden(k1_xboole_0,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0))) | ~spl4_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f335])).
% 0.20/0.50  fof(f668,plain,(
% 0.20/0.50    spl4_5 | ~spl4_1 | ~spl4_4 | spl4_62 | ~spl4_8 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f664,f197,f87,f666,f67,f52,f72])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl4_8 <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    spl4_16 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.50  fof(f664,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_tarski(k1_xboole_0)) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,k1_xboole_0) | v2_struct_0(sK0)) ) | (~spl4_8 | ~spl4_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f657,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f657,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(k6_domain_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_16),
% 0.20/0.50    inference(superposition,[],[f35,f199])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f197])).
% 0.20/0.50  fof(f663,plain,(
% 0.20/0.50    spl4_5 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_61 | ~spl4_8 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f659,f197,f87,f661,f67,f62,f57,f52,f72])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    spl4_2 <=> v5_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl4_3 <=> v4_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f659,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(k1_xboole_0)) | m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_8 | ~spl4_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f658,f89])).
% 0.20/0.50  fof(f658,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | (~spl4_8 | ~spl4_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f656,f89])).
% 0.20/0.50  fof(f656,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_16),
% 0.20/0.50    inference(superposition,[],[f43,f199])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 0.20/0.50  fof(f628,plain,(
% 0.20/0.50    ~spl4_59 | ~spl4_8 | ~spl4_16 | spl4_50),
% 0.20/0.50    inference(avatar_split_clause,[],[f623,f498,f197,f87,f625])).
% 0.20/0.50  fof(f498,plain,(
% 0.20/0.50    spl4_50 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.20/0.50  fof(f623,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_tarski(k1_xboole_0)) | (~spl4_8 | ~spl4_16 | spl4_50)),
% 0.20/0.50    inference(forward_demodulation,[],[f607,f89])).
% 0.20/0.50  fof(f607,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | (~spl4_16 | spl4_50)),
% 0.20/0.50    inference(backward_demodulation,[],[f499,f199])).
% 0.20/0.50  fof(f499,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | spl4_50),
% 0.20/0.50    inference(avatar_component_clause,[],[f498])).
% 0.20/0.50  fof(f597,plain,(
% 0.20/0.50    spl4_57 | spl4_5 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f592,f52,f67,f62,f57,f72,f595])).
% 0.20/0.50  fof(f592,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) ) | ~spl4_1),
% 0.20/0.50    inference(resolution,[],[f34,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    l1_orders_2(sK0) | ~spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f52])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k1_orders_2(X0,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).
% 0.20/0.50  fof(f518,plain,(
% 0.20/0.50    spl4_51 | ~spl4_50),
% 0.20/0.50    inference(avatar_split_clause,[],[f504,f498,f515])).
% 0.20/0.50  fof(f515,plain,(
% 0.20/0.50    spl4_51 <=> k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_50),
% 0.20/0.50    inference(resolution,[],[f500,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_50),
% 0.20/0.50    inference(avatar_component_clause,[],[f498])).
% 0.20/0.50  fof(f513,plain,(
% 0.20/0.50    ~spl4_46 | ~spl4_50),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f503])).
% 0.20/0.50  fof(f503,plain,(
% 0.20/0.50    $false | (~spl4_46 | ~spl4_50)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f50,f480,f500,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~r2_hidden(X2,X1)) )),
% 0.20/0.50    inference(resolution,[],[f39,f37])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f480,plain,(
% 0.20/0.50    m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_46),
% 0.20/0.50    inference(avatar_component_clause,[],[f478])).
% 0.20/0.50  fof(f478,plain,(
% 0.20/0.50    spl4_46 <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    spl4_37 | ~spl4_18 | ~spl4_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f360,f280,f217,f362])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    spl4_18 <=> m1_subset_1(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    spl4_25 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_xboole_0) | (~spl4_18 | ~spl4_25)),
% 0.20/0.50    inference(forward_demodulation,[],[f219,f282])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl4_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f280])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_xboole_0) | ~spl4_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f217])).
% 0.20/0.50  fof(f338,plain,(
% 0.20/0.50    spl4_32 | ~spl4_17 | ~spl4_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f305,f280,f212,f335])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    spl4_17 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    r2_hidden(k1_xboole_0,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,k1_xboole_0))) | (~spl4_17 | ~spl4_25)),
% 0.20/0.50    inference(backward_demodulation,[],[f214,f282])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1))) | ~spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f212])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    spl4_9 | spl4_10 | ~spl4_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f289,f82,f133,f130])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl4_9 <=> ! [X0] : ~r2_hidden(X0,u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f289,plain,(
% 0.20/0.50    ( ! [X0] : (k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl4_7),
% 0.20/0.50    inference(resolution,[],[f84,f108])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    spl4_25 | ~spl4_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f278,f255,f280])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    spl4_23 <=> v1_xboole_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl4_23),
% 0.20/0.50    inference(resolution,[],[f256,f33])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | ~spl4_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f255])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    ~spl4_18 | ~spl4_20 | spl4_23),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f263])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    $false | (~spl4_18 | ~spl4_20 | spl4_23)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f230,f219,f257,f39])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | spl4_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f255])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0) | ~spl4_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f228])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    spl4_20 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    spl4_20 | ~spl4_15 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f206,f197,f185,f228])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    spl4_15 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0) | (~spl4_15 | ~spl4_16)),
% 0.20/0.50    inference(backward_demodulation,[],[f187,f199])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f185])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl4_18 | ~spl4_7 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f202,f197,f82,f217])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_xboole_0) | (~spl4_7 | ~spl4_16)),
% 0.20/0.50    inference(backward_demodulation,[],[f84,f199])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    spl4_17 | ~spl4_6 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f201,f197,f77,f212])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1))) | (~spl4_6 | ~spl4_16)),
% 0.20/0.50    inference(backward_demodulation,[],[f79,f199])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    spl4_16 | ~spl4_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f195,f185,f197])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_15),
% 0.20/0.50    inference(resolution,[],[f187,f33])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    spl4_15 | ~spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f179,f130,f185])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f131,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f130])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f87])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl4_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f25,f82])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl4_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f26,f77])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f72])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f67])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f62])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f57])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f52])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (6917)------------------------------
% 0.20/0.50  % (6917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6917)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (6917)Memory used [KB]: 7164
% 0.20/0.50  % (6917)Time elapsed: 0.057 s
% 0.20/0.50  % (6917)------------------------------
% 0.20/0.50  % (6917)------------------------------
% 0.20/0.50  % (6907)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (6898)Success in time 0.145 s
%------------------------------------------------------------------------------
