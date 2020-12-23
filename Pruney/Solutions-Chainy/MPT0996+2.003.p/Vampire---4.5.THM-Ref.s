%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 150 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  219 ( 347 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f73,f110,f137,f148,f212,f246,f718])).

fof(f718,plain,
    ( ~ spl4_3
    | spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | ~ spl4_3
    | spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f211,f716])).

fof(f716,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),sK1)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f714,f93])).

fof(f93,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f72,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f714,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f286,f662,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f662,plain,
    ( ! [X0] : v5_relat_1(k7_relat_1(sK3,X0),sK1)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f396,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f396,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(superposition,[],[f282,f245])).

fof(f245,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_xboole_0(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl4_12
  <=> k2_zfmisc_1(sK0,sK1) = k2_xboole_0(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f282,plain,
    ( ! [X2,X3] : r1_tarski(k7_relat_1(sK3,X2),k2_xboole_0(sK3,X3))
    | ~ spl4_3 ),
    inference(superposition,[],[f126,f183])).

fof(f183,plain,
    ( ! [X0] : sK3 = k2_xboole_0(k7_relat_1(sK3,X0),sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f72,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_xboole_0(k7_relat_1(X1,X2),X1) = X1 ) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f126,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(unit_resulting_resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f49,f46])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f286,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f95,f216])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | v1_relat_1(X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f98,f45])).

fof(f98,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK3))
        | v1_relat_1(X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f95,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f72,f36])).

fof(f211,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl4_10
  <=> r1_tarski(k9_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f246,plain,
    ( spl4_12
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f111,f107,f243])).

fof(f107,plain,
    ( spl4_5
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f111,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_xboole_0(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f109,f40])).

fof(f109,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f212,plain,
    ( ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f149,f145,f209])).

fof(f145,plain,
    ( spl4_8
  <=> m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f149,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),sK1)
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f147,f45])).

fof(f147,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( ~ spl4_8
    | ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f138,f134,f52,f145])).

fof(f52,plain,
    ( spl4_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( spl4_6
  <=> m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f138,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_1
    | spl4_6 ),
    inference(forward_demodulation,[],[f136,f90])).

fof(f90,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f54,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f136,plain,
    ( ~ m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f137,plain,
    ( ~ spl4_6
    | spl4_2 ),
    inference(avatar_split_clause,[],[f62,f57,f134])).

fof(f57,plain,
    ( spl4_2
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( ~ m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f110,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f52,f107])).

fof(f63,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f54,f44])).

fof(f73,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f67,f52,f70])).

fof(f67,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f35,f54,f34])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f60,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

fof(f55,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f32,f52])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:04:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.41  % (9445)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.42  % (9454)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.42  % (9446)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.43  % (9436)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.43  % (9436)Refutation not found, incomplete strategy% (9436)------------------------------
% 0.19/0.43  % (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (9437)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.44  % (9453)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.44  % (9436)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (9436)Memory used [KB]: 10490
% 0.19/0.44  % (9436)Time elapsed: 0.077 s
% 0.19/0.44  % (9436)------------------------------
% 0.19/0.44  % (9436)------------------------------
% 0.19/0.44  % (9454)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f721,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f55,f60,f73,f110,f137,f148,f212,f246,f718])).
% 0.19/0.44  fof(f718,plain,(
% 0.19/0.44    ~spl4_3 | spl4_10 | ~spl4_12),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f717])).
% 0.19/0.44  fof(f717,plain,(
% 0.19/0.44    $false | (~spl4_3 | spl4_10 | ~spl4_12)),
% 0.19/0.44    inference(subsumption_resolution,[],[f211,f716])).
% 0.19/0.44  fof(f716,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),sK1)) ) | (~spl4_3 | ~spl4_12)),
% 0.19/0.44    inference(forward_demodulation,[],[f714,f93])).
% 0.19/0.44  fof(f93,plain,(
% 0.19/0.44    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_3),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f72,f37])).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f20])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.44  fof(f72,plain,(
% 0.19/0.44    v1_relat_1(sK3) | ~spl4_3),
% 0.19/0.44    inference(avatar_component_clause,[],[f70])).
% 0.19/0.44  fof(f70,plain,(
% 0.19/0.44    spl4_3 <=> v1_relat_1(sK3)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.44  fof(f714,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_3 | ~spl4_12)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f286,f662,f38])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f28])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(nnf_transformation,[],[f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.44  fof(f662,plain,(
% 0.19/0.44    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK1)) ) | (~spl4_3 | ~spl4_12)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f396,f87])).
% 0.19/0.44  fof(f87,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f47,f45])).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f31])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.44    inference(nnf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.44  fof(f47,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.44    inference(pure_predicate_removal,[],[f10])).
% 0.19/0.44  fof(f10,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.44  fof(f396,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1))) ) | (~spl4_3 | ~spl4_12)),
% 0.19/0.44    inference(superposition,[],[f282,f245])).
% 0.19/0.44  fof(f245,plain,(
% 0.19/0.44    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_12),
% 0.19/0.44    inference(avatar_component_clause,[],[f243])).
% 0.19/0.44  fof(f243,plain,(
% 0.19/0.44    spl4_12 <=> k2_zfmisc_1(sK0,sK1) = k2_xboole_0(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.44  fof(f282,plain,(
% 0.19/0.44    ( ! [X2,X3] : (r1_tarski(k7_relat_1(sK3,X2),k2_xboole_0(sK3,X3))) ) | ~spl4_3),
% 0.19/0.44    inference(superposition,[],[f126,f183])).
% 0.19/0.44  fof(f183,plain,(
% 0.19/0.44    ( ! [X0] : (sK3 = k2_xboole_0(k7_relat_1(sK3,X0),sK3)) ) | ~spl4_3),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f72,f76])).
% 0.19/0.44  fof(f76,plain,(
% 0.19/0.44    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_xboole_0(k7_relat_1(X1,X2),X1) = X1) )),
% 0.19/0.44    inference(resolution,[],[f40,f36])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.19/0.44  fof(f40,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.44  fof(f126,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f78,f46])).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.19/0.44  fof(f78,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f49,f46])).
% 0.19/0.44  fof(f49,plain,(
% 0.19/0.44    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.44    inference(equality_resolution,[],[f42])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.44    inference(cnf_transformation,[],[f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.44    inference(flattening,[],[f29])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.44    inference(nnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.44  fof(f286,plain,(
% 0.19/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_3),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f95,f216])).
% 0.19/0.44  fof(f216,plain,(
% 0.19/0.44    ( ! [X0] : (~r1_tarski(X0,sK3) | v1_relat_1(X0)) ) | ~spl4_3),
% 0.19/0.44    inference(resolution,[],[f98,f45])).
% 0.19/0.44  fof(f98,plain,(
% 0.19/0.44    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK3)) | v1_relat_1(X2)) ) | ~spl4_3),
% 0.19/0.44    inference(resolution,[],[f72,f34])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.44  fof(f95,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) ) | ~spl4_3),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f72,f36])).
% 0.19/0.44  fof(f211,plain,(
% 0.19/0.44    ~r1_tarski(k9_relat_1(sK3,sK2),sK1) | spl4_10),
% 0.19/0.44    inference(avatar_component_clause,[],[f209])).
% 0.19/0.44  fof(f209,plain,(
% 0.19/0.44    spl4_10 <=> r1_tarski(k9_relat_1(sK3,sK2),sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.44  fof(f246,plain,(
% 0.19/0.44    spl4_12 | ~spl4_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f111,f107,f243])).
% 0.19/0.44  fof(f107,plain,(
% 0.19/0.44    spl4_5 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.44  fof(f111,plain,(
% 0.19/0.44    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f109,f40])).
% 0.19/0.44  fof(f109,plain,(
% 0.19/0.44    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 0.19/0.44    inference(avatar_component_clause,[],[f107])).
% 0.19/0.44  fof(f212,plain,(
% 0.19/0.44    ~spl4_10 | spl4_8),
% 0.19/0.44    inference(avatar_split_clause,[],[f149,f145,f209])).
% 0.19/0.44  fof(f145,plain,(
% 0.19/0.44    spl4_8 <=> m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.44  fof(f149,plain,(
% 0.19/0.44    ~r1_tarski(k9_relat_1(sK3,sK2),sK1) | spl4_8),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f147,f45])).
% 0.19/0.44  fof(f147,plain,(
% 0.19/0.44    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(sK1)) | spl4_8),
% 0.19/0.44    inference(avatar_component_clause,[],[f145])).
% 0.19/0.44  fof(f148,plain,(
% 0.19/0.44    ~spl4_8 | ~spl4_1 | spl4_6),
% 0.19/0.44    inference(avatar_split_clause,[],[f138,f134,f52,f145])).
% 0.19/0.44  fof(f52,plain,(
% 0.19/0.44    spl4_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.44  fof(f134,plain,(
% 0.19/0.44    spl4_6 <=> m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.44  fof(f138,plain,(
% 0.19/0.44    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(sK1)) | (~spl4_1 | spl4_6)),
% 0.19/0.44    inference(forward_demodulation,[],[f136,f90])).
% 0.19/0.44  fof(f90,plain,(
% 0.19/0.44    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f54,f48])).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,axiom,(
% 0.19/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f52])).
% 0.19/0.44  fof(f136,plain,(
% 0.19/0.44    ~m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(sK1)) | spl4_6),
% 0.19/0.44    inference(avatar_component_clause,[],[f134])).
% 0.19/0.44  fof(f137,plain,(
% 0.19/0.44    ~spl4_6 | spl4_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f62,f57,f134])).
% 0.19/0.44  fof(f57,plain,(
% 0.19/0.44    spl4_2 <=> r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    ~m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(sK1)) | spl4_2),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f59,f44])).
% 0.19/0.44  fof(f44,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f31])).
% 0.19/0.44  fof(f59,plain,(
% 0.19/0.44    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) | spl4_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f57])).
% 0.19/0.44  fof(f110,plain,(
% 0.19/0.44    spl4_5 | ~spl4_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f63,f52,f107])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f54,f44])).
% 0.19/0.44  fof(f73,plain,(
% 0.19/0.44    spl4_3 | ~spl4_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f67,f52,f70])).
% 0.19/0.44  fof(f67,plain,(
% 0.19/0.44    v1_relat_1(sK3) | ~spl4_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f35,f54,f34])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.44  fof(f60,plain,(
% 0.19/0.44    ~spl4_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f33,f57])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f27])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f26])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.19/0.44    inference(pure_predicate_removal,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.19/0.44    inference(pure_predicate_removal,[],[f13])).
% 0.19/0.44  fof(f13,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.19/0.44    inference(negated_conjecture,[],[f12])).
% 0.19/0.44  fof(f12,conjecture,(
% 0.19/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).
% 0.19/0.44  fof(f55,plain,(
% 0.19/0.44    spl4_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f32,f52])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.44    inference(cnf_transformation,[],[f27])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (9454)------------------------------
% 0.19/0.44  % (9454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (9454)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (9454)Memory used [KB]: 11129
% 0.19/0.44  % (9454)Time elapsed: 0.058 s
% 0.19/0.44  % (9454)------------------------------
% 0.19/0.44  % (9454)------------------------------
% 0.19/0.45  % (9428)Success in time 0.112 s
%------------------------------------------------------------------------------
