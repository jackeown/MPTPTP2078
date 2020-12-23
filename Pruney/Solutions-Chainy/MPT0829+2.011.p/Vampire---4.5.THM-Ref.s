%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 159 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 410 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f73,f97,f124,f145,f150,f156,f162,f176,f181,f221,f236])).

fof(f236,plain,
    ( spl3_5
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl3_5
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f234,f182])).

fof(f182,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f72,f175])).

fof(f175,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl3_13
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f72,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f234,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f233,f220])).

fof(f220,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_17
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f233,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f180,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f180,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f221,plain,
    ( spl3_17
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f127,f121,f218])).

fof(f121,plain,
    ( spl3_8
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f123,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f123,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f181,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f112,f94,f46,f178])).

fof(f46,plain,
    ( spl3_1
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f94,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f112,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f103,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f103,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f29,f48,f96,f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f96,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f48,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f176,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f90,f51,f173])).

fof(f51,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f90,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f162,plain,
    ( ~ spl3_9
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f158,f144])).

fof(f144,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f158,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl3_11 ),
    inference(resolution,[],[f155,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f155,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f156,plain,
    ( ~ spl3_11
    | ~ spl3_2
    | spl3_10 ),
    inference(avatar_split_clause,[],[f151,f147,f51,f153])).

fof(f147,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f151,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl3_2
    | spl3_10 ),
    inference(forward_demodulation,[],[f149,f87])).

fof(f87,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f150,plain,
    ( ~ spl3_10
    | spl3_4 ),
    inference(avatar_split_clause,[],[f74,f66,f147])).

fof(f66,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2)))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f68,f37])).

fof(f68,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f145,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f111,f94,f46,f142])).

fof(f111,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f106,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f106,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f29,f48,f96,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f101,f51,f121])).

fof(f101,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f98,f90])).

fof(f98,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f97,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f51,f94])).

fof(f75,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f53,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f73,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f28,f70,f66])).

fof(f28,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).

fof(f21,plain,
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

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f46])).

fof(f27,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:09:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (7011)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (7018)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (7018)Refutation not found, incomplete strategy% (7018)------------------------------
% 0.21/0.49  % (7018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7011)Refutation not found, incomplete strategy% (7011)------------------------------
% 0.21/0.49  % (7011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7011)Memory used [KB]: 10618
% 0.21/0.49  % (7011)Time elapsed: 0.060 s
% 0.21/0.49  % (7011)------------------------------
% 0.21/0.49  % (7011)------------------------------
% 0.21/0.49  % (7018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7018)Memory used [KB]: 6268
% 0.21/0.49  % (7018)Time elapsed: 0.064 s
% 0.21/0.49  % (7018)------------------------------
% 0.21/0.49  % (7018)------------------------------
% 0.21/0.51  % (7004)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (7028)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (7028)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f49,f54,f73,f97,f124,f145,f150,f156,f162,f176,f181,f221,f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl3_5 | ~spl3_13 | ~spl3_14 | ~spl3_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    $false | (spl3_5 | ~spl3_13 | ~spl3_14 | ~spl3_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    sK1 != k2_relat_1(sK2) | (spl3_5 | ~spl3_13)),
% 0.21/0.52    inference(superposition,[],[f72,f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    spl3_13 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    sK1 = k2_relat_1(sK2) | (~spl3_14 | ~spl3_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f233,f220])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f218])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl3_17 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK2),sK1) | sK1 = k2_relat_1(sK2) | ~spl3_14),
% 0.21/0.52    inference(resolution,[],[f180,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl3_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl3_14 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl3_17 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f127,f121,f218])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl3_8 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_8),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f123,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl3_14 | ~spl3_1 | ~spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f94,f46,f178])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl3_1 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl3_6 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r1_tarski(sK1,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f103,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f29,f48,f96,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f94])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    r1_tarski(k6_relat_1(sK1),sK2) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl3_13 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f90,f51,f173])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ~spl3_9 | spl3_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    $false | (~spl3_9 | spl3_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    r1_tarski(sK1,k1_relat_1(sK2)) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl3_9 <=> r1_tarski(sK1,k1_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl3_11),
% 0.21/0.52    inference(resolution,[],[f155,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) | spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl3_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~spl3_11 | ~spl3_2 | spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f151,f147,f51,f153])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl3_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) | (~spl3_2 | spl3_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f149,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2))) | spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f147])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~spl3_10 | spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f74,f66,f147])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_4 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2))) | spl3_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f68,f37])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl3_9 | ~spl3_1 | ~spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f111,f94,f46,f142])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r1_tarski(sK1,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f106,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f29,f48,f96,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl3_8 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f101,f51,f121])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_2),
% 0.21/0.52    inference(forward_demodulation,[],[f98,f90])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl3_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl3_6 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f51,f94])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~spl3_4 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f70,f66])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f46])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7028)------------------------------
% 0.21/0.52  % (7028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7028)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7028)Memory used [KB]: 10746
% 0.21/0.52  % (7028)Time elapsed: 0.097 s
% 0.21/0.52  % (7028)------------------------------
% 0.21/0.52  % (7028)------------------------------
% 0.21/0.52  % (7002)Success in time 0.152 s
%------------------------------------------------------------------------------
