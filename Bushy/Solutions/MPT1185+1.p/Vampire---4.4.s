%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t136_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:17 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 609 expanded)
%              Number of leaves         :   54 ( 244 expanded)
%              Depth                    :   12
%              Number of atoms          :  721 (2012 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f133,f140,f147,f154,f161,f168,f175,f182,f192,f204,f225,f234,f243,f253,f274,f283,f293,f306,f319,f334,f342,f350,f359,f367,f378,f386,f394,f404,f416,f425,f437,f439,f441,f443,f445,f447,f449,f455])).

fof(f455,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f453,f305])).

fof(f305,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl4_36
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f453,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_15
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f452,f377])).

fof(f377,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl4_50
  <=> r1_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f452,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_15
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f451,f333])).

fof(f333,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl4_40
  <=> r8_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f451,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_15
    | ~ spl4_46
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f450,f358])).

fof(f358,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl4_46
  <=> r4_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f450,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_15
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f436,f174])).

fof(f174,plain,
    ( ~ r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_15
  <=> ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f436,plain,
    ( r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_58 ),
    inference(resolution,[],[f92,f415])).

fof(f415,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl4_58
  <=> r6_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X0,X1)
      | r3_orders_1(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d8_orders_1)).

fof(f449,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f429,f415])).

fof(f429,plain,
    ( ~ r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f305,f377,f333,f358,f174,f92])).

fof(f447,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f430,f174])).

fof(f430,plain,
    ( r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f305,f377,f333,f358,f415,f92])).

fof(f445,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f431,f358])).

fof(f431,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f305,f377,f333,f174,f415,f92])).

fof(f443,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f432,f333])).

fof(f432,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f305,f377,f358,f174,f415,f92])).

fof(f441,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f433,f377])).

fof(f433,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f305,f333,f358,f174,f415,f92])).

fof(f439,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f434,f305])).

fof(f434,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_15
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f377,f333,f358,f174,f415,f92])).

fof(f437,plain,
    ( spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_40
    | ~ spl4_46
    | ~ spl4_50
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f305,f377,f333,f358,f174,f415,f92])).

fof(f425,plain,
    ( spl4_60
    | ~ spl4_26
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f371,f304,f241,f423])).

fof(f423,plain,
    ( spl4_60
  <=> r1_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f241,plain,
    ( spl4_26
  <=> r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f371,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_26
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f305,f242,f196,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( r1_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( r1_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r1_relat_2(X2,X0) )
       => r1_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t93_orders_1)).

fof(f196,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f103,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t3_subset)).

fof(f103,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',existence_m1_subset_1)).

fof(f242,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f416,plain,
    ( spl4_58
    | ~ spl4_36
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f407,f402,f304,f414])).

fof(f402,plain,
    ( spl4_56
  <=> r7_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f407,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_36
    | ~ spl4_56 ),
    inference(unit_resulting_resolution,[],[f305,f403,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r7_relat_2(X1,X0)
      | r6_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t92_orders_1)).

fof(f403,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f402])).

fof(f404,plain,
    ( spl4_56
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f395,f180,f166,f145,f402])).

fof(f145,plain,
    ( spl4_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f166,plain,
    ( spl4_12
  <=> v6_orders_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f180,plain,
    ( spl4_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f395,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f146,f167,f181,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d11_orders_2)).

fof(f181,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f167,plain,
    ( v6_orders_2(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f146,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f394,plain,
    ( spl4_54
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f352,f304,f223,f392])).

fof(f392,plain,
    ( spl4_54
  <=> r4_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f223,plain,
    ( spl4_22
  <=> r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f352,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f305,f224,f196,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t94_orders_1)).

fof(f224,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f223])).

fof(f386,plain,
    ( spl4_52
    | ~ spl4_36
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f379,f376,f304,f384])).

fof(f384,plain,
    ( spl4_52
  <=> r1_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f379,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(sK1)))
    | ~ spl4_36
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f196,f305,f377,f115])).

fof(f378,plain,
    ( spl4_50
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f370,f304,f241,f202,f376])).

fof(f202,plain,
    ( spl4_20
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f370,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f305,f242,f203,f115])).

fof(f203,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f367,plain,
    ( spl4_48
    | ~ spl4_36
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f360,f357,f304,f365])).

fof(f365,plain,
    ( spl4_48
  <=> r4_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f360,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(sK1)))
    | ~ spl4_36
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f196,f305,f358,f114])).

fof(f359,plain,
    ( spl4_46
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f351,f304,f223,f202,f357])).

fof(f351,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f305,f224,f203,f114])).

fof(f350,plain,
    ( spl4_44
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f327,f304,f232,f348])).

fof(f348,plain,
    ( spl4_44
  <=> r8_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f232,plain,
    ( spl4_24
  <=> r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f327,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f305,f233,f196,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t95_orders_1)).

fof(f233,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f342,plain,
    ( spl4_42
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f335,f332,f304,f340])).

fof(f340,plain,
    ( spl4_42
  <=> r8_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f335,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK2(k1_zfmisc_1(sK1)))
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f196,f305,f333,f113])).

fof(f334,plain,
    ( spl4_40
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f326,f304,f232,f202,f332])).

fof(f326,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f305,f233,f203,f113])).

fof(f319,plain,
    ( spl4_38
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f297,f159,f317])).

fof(f317,plain,
    ( spl4_38
  <=> v1_relat_1(u1_orders_2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f159,plain,
    ( spl4_10
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f297,plain,
    ( v1_relat_1(u1_orders_2(sK3))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f160,f286])).

fof(f286,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f94,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',cc1_relset_1)).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',dt_u1_orders_2)).

fof(f160,plain,
    ( l1_orders_2(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f306,plain,
    ( spl4_36
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f296,f145,f304])).

fof(f296,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f146,f286])).

fof(f293,plain,
    ( spl4_34
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f276,f272,f291])).

fof(f291,plain,
    ( spl4_34
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f272,plain,
    ( spl4_30
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f276,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_30 ),
    inference(superposition,[],[f103,f273])).

fof(f273,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f272])).

fof(f283,plain,
    ( spl4_32
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f275,f272,f281])).

fof(f281,plain,
    ( spl4_32
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f275,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_30 ),
    inference(superposition,[],[f196,f273])).

fof(f274,plain,
    ( spl4_30
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f259,f251,f152,f272])).

fof(f152,plain,
    ( spl4_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f251,plain,
    ( spl4_28
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f259,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f252,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f183,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t6_boole)).

fof(f183,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f93])).

fof(f153,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f252,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( spl4_28
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f246,f152,f251])).

fof(f246,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f103,f245,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t2_subset)).

fof(f245,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f103,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t5_subset)).

fof(f243,plain,
    ( spl4_26
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f236,f145,f124,f241])).

fof(f124,plain,
    ( spl4_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f236,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f146,f125,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d4_orders_2)).

fof(f125,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f124])).

fof(f234,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f227,f145,f131,f232])).

fof(f131,plain,
    ( spl4_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f227,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f146,f132,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d5_orders_2)).

fof(f132,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f225,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f218,f145,f138,f223])).

fof(f138,plain,
    ( spl4_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f218,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f146,f139,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',d6_orders_2)).

fof(f139,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f204,plain,
    ( spl4_20
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f197,f180,f202])).

fof(f197,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f181,f110])).

fof(f192,plain,
    ( spl4_18
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f183,f152,f190])).

fof(f190,plain,
    ( spl4_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f182,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f85,f180])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ r3_orders_1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v6_orders_2(sK1,sK0)
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f66,f65])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v6_orders_2(X1,sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
     => ( ~ r3_orders_1(u1_orders_2(X0),sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',t136_orders_2)).

fof(f175,plain,(
    ~ spl4_15 ),
    inference(avatar_split_clause,[],[f86,f173])).

fof(f86,plain,(
    ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f168,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f84,f166])).

fof(f84,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f161,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f119,f159])).

fof(f119,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f78])).

fof(f78,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK3) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',existence_l1_orders_2)).

fof(f154,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f87,f152])).

fof(f87,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t136_orders_2.p',dt_o_0_0_xboole_0)).

fof(f147,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f83,f145])).

fof(f83,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f140,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f82,f138])).

fof(f82,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f133,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f81,f131])).

fof(f81,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f126,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f80,f124])).

fof(f80,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
