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
% DateTime   : Thu Dec  3 12:56:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 174 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 ( 463 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f72,f93,f110,f119,f141,f146,f152,f164,f187,f224,f231,f236])).

fof(f236,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_16
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_16
    | spl3_17 ),
    inference(subsumption_resolution,[],[f234,f230])).

fof(f230,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl3_17
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f234,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f233,f188])).

fof(f188,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f176,f29])).

fof(f29,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f176,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f92,f47,f140,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f140,plain,
    ( v1_relat_1(k6_relat_1(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_9
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f47,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f92,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f233,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f223,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f223,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_16
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f231,plain,
    ( ~ spl3_17
    | spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f193,f161,f69,f228])).

fof(f69,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f161,plain,
    ( spl3_13
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f193,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f71,f163])).

fof(f163,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f71,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f224,plain,
    ( spl3_16
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f123,f116,f221])).

fof(f116,plain,
    ( spl3_8
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f123,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f118,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f118,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f187,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f185,f153])).

fof(f153,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f151,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f151,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f185,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f179,f28])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f179,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f92,f47,f140,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f164,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f86,f50,f161])).

fof(f50,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f152,plain,
    ( ~ spl3_11
    | ~ spl3_2
    | spl3_10 ),
    inference(avatar_split_clause,[],[f147,f143,f50,f149])).

fof(f143,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl3_2
    | spl3_10 ),
    inference(forward_demodulation,[],[f145,f83])).

fof(f83,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f146,plain,
    ( ~ spl3_10
    | spl3_4 ),
    inference(avatar_split_clause,[],[f73,f65,f143])).

fof(f65,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2)))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f67,f37])).

fof(f67,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f141,plain,
    ( spl3_9
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f120,f107,f90,f138])).

fof(f107,plain,
    ( spl3_7
  <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f120,plain,
    ( v1_relat_1(k6_relat_1(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f92,f109,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f109,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f119,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f97,f50,f116])).

fof(f97,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f94,f86])).

fof(f94,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f110,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f56,f45,f107])).

fof(f56,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f47,f38])).

fof(f93,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f50,f90])).

fof(f74,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f33,f52,f32])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f27,f69,f65])).

fof(f27,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).

fof(f20,plain,
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

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f26,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:05:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (20209)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (20228)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (20206)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (20205)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (20206)Refutation not found, incomplete strategy% (20206)------------------------------
% 0.22/0.51  % (20206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20206)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20206)Memory used [KB]: 10618
% 0.22/0.51  % (20206)Time elapsed: 0.091 s
% 0.22/0.51  % (20206)------------------------------
% 0.22/0.51  % (20206)------------------------------
% 0.22/0.51  % (20208)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (20228)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f48,f53,f72,f93,f110,f119,f141,f146,f152,f164,f187,f224,f231,f236])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_6 | ~spl3_9 | ~spl3_16 | spl3_17),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    $false | (~spl3_1 | ~spl3_6 | ~spl3_9 | ~spl3_16 | spl3_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f234,f230])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    sK1 != k2_relat_1(sK2) | spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    spl3_17 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | (~spl3_1 | ~spl3_6 | ~spl3_9 | ~spl3_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f233,f188])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    r1_tarski(sK1,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f176,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f92,f47,f140,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    v1_relat_1(k6_relat_1(sK1)) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl3_9 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    r1_tarski(k6_relat_1(sK1),sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    spl3_1 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl3_6 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~spl3_16),
% 0.22/0.51    inference(resolution,[],[f223,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl3_16 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ~spl3_17 | spl3_5 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f193,f161,f69,f228])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl3_13 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    sK1 != k2_relat_1(sK2) | (spl3_5 | ~spl3_13)),
% 0.22/0.51    inference(superposition,[],[f71,f163])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f161])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl3_16 | ~spl3_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f123,f116,f221])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl3_8 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_8),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f118,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_6 | ~spl3_9 | spl3_11),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    $false | (~spl3_1 | ~spl3_6 | ~spl3_9 | spl3_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f185,f153])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl3_11),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f151,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) | spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    spl3_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    r1_tarski(sK1,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f179,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f92,f47,f140,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    spl3_13 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f86,f50,f161])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~spl3_11 | ~spl3_2 | spl3_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f147,f143,f50,f149])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl3_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) | (~spl3_2 | spl3_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f145,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2))) | spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f143])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~spl3_10 | spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f73,f65,f143])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl3_4 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relset_1(sK0,sK1,sK2))) | spl3_4),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f67,f37])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl3_9 | ~spl3_6 | ~spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f120,f107,f90,f138])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl3_7 <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    v1_relat_1(k6_relat_1(sK1)) | (~spl3_6 | ~spl3_7)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f92,f109,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2)) | ~spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f107])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_8 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f97,f50,f116])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_2),
% 0.22/0.51    inference(forward_demodulation,[],[f94,f86])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl3_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl3_7 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f45,f107])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2)) | ~spl3_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f47,f38])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl3_6 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f74,f50,f90])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f33,f52,f32])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f69,f65])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f50])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f45])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (20228)------------------------------
% 0.22/0.51  % (20228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20228)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (20228)Memory used [KB]: 10746
% 0.22/0.51  % (20228)Time elapsed: 0.086 s
% 0.22/0.51  % (20228)------------------------------
% 0.22/0.51  % (20228)------------------------------
% 0.22/0.51  % (20202)Success in time 0.145 s
%------------------------------------------------------------------------------
