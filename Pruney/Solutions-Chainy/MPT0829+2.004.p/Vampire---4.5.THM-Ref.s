%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 141 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  237 ( 378 expanded)
%              Number of equality atoms :   37 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f64,f90,f107,f119,f124,f127,f170,f175,f182,f189])).

fof(f189,plain,
    ( ~ spl3_13
    | ~ spl3_14
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_14
    | spl3_15 ),
    inference(subsumption_resolution,[],[f187,f181])).

fof(f181,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_15
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f187,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f186,f174])).

fof(f174,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_14
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f186,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f169,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f169,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_13
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f182,plain,
    ( ~ spl3_15
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f134,f121,f61,f179])).

fof(f61,plain,
    ( spl3_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( spl3_8
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f134,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f63,f123])).

fof(f123,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f63,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f175,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f108,f104,f87,f172])).

fof(f87,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( spl3_6
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f108,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f89,f106,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f106,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f89,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f170,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f102,f87,f47,f167])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f91,f32])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f91,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f30,f49,f89,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f49,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f127,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f125,f101])).

fof(f101,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f94,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f94,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f30,f49,f89,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f59,f118])).

fof(f118,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_7
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f59,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_3
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f84,f52,f121])).

fof(f52,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f84,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f119,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f52,f116])).

fof(f82,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f107,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f52,f104])).

fof(f74,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f90,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f52,f87])).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f64,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f29,f61,f57])).

fof(f29,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f47])).

fof(f28,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (6348)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.43  % (6348)Refutation not found, incomplete strategy% (6348)------------------------------
% 0.21/0.43  % (6348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (6348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (6348)Memory used [KB]: 10618
% 0.21/0.43  % (6348)Time elapsed: 0.006 s
% 0.21/0.43  % (6348)------------------------------
% 0.21/0.43  % (6348)------------------------------
% 0.21/0.47  % (6360)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.48  % (6360)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f50,f55,f64,f90,f107,f119,f124,f127,f170,f175,f182,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl3_13 | ~spl3_14 | spl3_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    $false | (~spl3_13 | ~spl3_14 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    sK1 != k2_relat_1(sK2) | spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    spl3_15 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | (~spl3_13 | ~spl3_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f174])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl3_14 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK2),sK1) | sK1 = k2_relat_1(sK2) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f169,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl3_13 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~spl3_15 | spl3_4 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f134,f121,f61,f179])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl3_8 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    sK1 != k2_relat_1(sK2) | (spl3_4 | ~spl3_8)),
% 0.21/0.48    inference(superposition,[],[f63,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl3_14 | ~spl3_5 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f108,f104,f87,f172])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl3_6 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_5 | ~spl3_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f89,f106,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    v5_relat_1(sK2,sK1) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl3_13 | ~spl3_1 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f102,f87,f47,f167])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_1 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    r1_tarski(sK1,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f91,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f30,f49,f89,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    r1_tarski(k6_relat_1(sK1),sK2) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    $false | (~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    r1_tarski(sK1,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f94,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f30,f49,f89,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k1_relat_1(sK2)) | (spl3_3 | ~spl3_7)),
% 0.21/0.48    inference(superposition,[],[f59,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl3_7 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_3 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl3_8 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f52,f121])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f54,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl3_7 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f82,f52,f116])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f54,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl3_6 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f52,f104])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    v5_relat_1(sK2,sK1) | ~spl3_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f54,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_5 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f65,f52,f87])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f54,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f61,f57])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f52])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f47])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6360)------------------------------
% 0.21/0.48  % (6360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6360)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6360)Memory used [KB]: 10746
% 0.21/0.48  % (6360)Time elapsed: 0.059 s
% 0.21/0.48  % (6360)------------------------------
% 0.21/0.48  % (6360)------------------------------
% 0.21/0.48  % (6335)Success in time 0.121 s
%------------------------------------------------------------------------------
