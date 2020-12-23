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
% DateTime   : Thu Dec  3 12:54:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 175 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :    7
%              Number of atoms          :  305 ( 457 expanded)
%              Number of equality atoms :   86 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f47,f51,f55,f59,f63,f67,f71,f75,f79,f85,f92,f98,f103,f110,f117,f123,f143,f152])).

fof(f152,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f150,f46])).

fof(f46,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f150,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_1
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f148,f37])).

fof(f37,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f148,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(superposition,[],[f134,f122])).

fof(f122,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_18
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) != k7_relat_1(X1,X0)
        | k9_relat_1(X1,X0) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = X0
        | k6_relat_1(X0) != k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f143,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f142,f107,f90,f73,f45,f133])).

fof(f73,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
        | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f90,plain,
    ( spl2_13
  <=> ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f107,plain,
    ( spl2_16
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X1,X0) = X0
        | k6_relat_1(X0) != k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f141,f91])).

fof(f91,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) != k7_relat_1(X1,X0)
        | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f126,f46])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) != k7_relat_1(X1,X0)
        | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(superposition,[],[f74,f108])).

fof(f108,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
        | k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f123,plain,
    ( spl2_18
    | ~ spl2_12
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f118,f115,f82,f120])).

fof(f82,plain,
    ( spl2_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f115,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f118,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_12
    | ~ spl2_17 ),
    inference(resolution,[],[f116,f84])).

fof(f84,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f113,f101,f69,f49,f45,f115])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f101,plain,
    ( spl2_15
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f112,f102])).

fof(f102,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f111,f46])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(superposition,[],[f70,f50])).

fof(f50,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f110,plain,
    ( spl2_16
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f105,f101,f96,f107])).

fof(f96,plain,
    ( spl2_14
  <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f105,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(superposition,[],[f97,f102])).

fof(f97,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f103,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f99,f65,f45,f101])).

fof(f65,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f99,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f66,f46])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f98,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f94,f61,f49,f45,f96])).

fof(f61,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f94,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f93,f50])).

fof(f93,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f92,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f88,f57,f53,f49,f45,f90])).

fof(f53,plain,
    ( spl2_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f57,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f88,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f87,f50])).

fof(f87,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f86,f54])).

fof(f54,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f86,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f85,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f80,f77,f40,f82])).

fof(f40,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f77,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f80,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f78,f42])).

fof(f42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f75,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
      | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
          | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
          | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
           => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f67,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f63,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f59,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f55,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f43,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (8004)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (8000)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (8004)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f38,f43,f47,f51,f55,f59,f63,f67,f71,f75,f79,f85,f92,f98,f103,f110,f117,f123,f143,f152])).
% 0.22/0.43  fof(f152,plain,(
% 0.22/0.43    spl2_1 | ~spl2_3 | ~spl2_18 | ~spl2_19),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.43  fof(f151,plain,(
% 0.22/0.43    $false | (spl2_1 | ~spl2_3 | ~spl2_18 | ~spl2_19)),
% 0.22/0.43    inference(subsumption_resolution,[],[f150,f46])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    ~v1_relat_1(k6_relat_1(sK0)) | (spl2_1 | ~spl2_18 | ~spl2_19)),
% 0.22/0.43    inference(subsumption_resolution,[],[f148,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f148,plain,(
% 0.22/0.43    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | (~spl2_18 | ~spl2_19)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f147])).
% 0.22/0.43  fof(f147,plain,(
% 0.22/0.43    k6_relat_1(sK1) != k6_relat_1(sK1) | sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | (~spl2_18 | ~spl2_19)),
% 0.22/0.43    inference(superposition,[],[f134,f122])).
% 0.22/0.43  fof(f122,plain,(
% 0.22/0.43    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl2_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f120])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    spl2_18 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.43  fof(f134,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) != k7_relat_1(X1,X0) | k9_relat_1(X1,X0) = X0 | ~v1_relat_1(X1)) ) | ~spl2_19),
% 0.22/0.43    inference(avatar_component_clause,[],[f133])).
% 0.22/0.43  fof(f133,plain,(
% 0.22/0.43    spl2_19 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = X0 | k6_relat_1(X0) != k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    spl2_19 | ~spl2_3 | ~spl2_10 | ~spl2_13 | ~spl2_16),
% 0.22/0.43    inference(avatar_split_clause,[],[f142,f107,f90,f73,f45,f133])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl2_10 <=> ! [X1,X0,X2] : (k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    spl2_13 <=> ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.43  fof(f107,plain,(
% 0.22/0.43    spl2_16 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.43  fof(f142,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k9_relat_1(X1,X0) = X0 | k6_relat_1(X0) != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | (~spl2_3 | ~spl2_10 | ~spl2_13 | ~spl2_16)),
% 0.22/0.43    inference(forward_demodulation,[],[f141,f91])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) ) | ~spl2_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f90])).
% 0.22/0.43  fof(f141,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) != k7_relat_1(X1,X0) | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(X1)) ) | (~spl2_3 | ~spl2_10 | ~spl2_16)),
% 0.22/0.43    inference(subsumption_resolution,[],[f126,f46])).
% 0.22/0.43  fof(f126,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) != k7_relat_1(X1,X0) | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | (~spl2_10 | ~spl2_16)),
% 0.22/0.43    inference(superposition,[],[f74,f108])).
% 0.22/0.43  fof(f108,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_16),
% 0.22/0.43    inference(avatar_component_clause,[],[f107])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X2,X0) | k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f73])).
% 0.22/0.43  fof(f123,plain,(
% 0.22/0.43    spl2_18 | ~spl2_12 | ~spl2_17),
% 0.22/0.43    inference(avatar_split_clause,[],[f118,f115,f82,f120])).
% 0.22/0.43  fof(f82,plain,(
% 0.22/0.43    spl2_12 <=> r1_tarski(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.43  fof(f115,plain,(
% 0.22/0.43    spl2_17 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_12 | ~spl2_17)),
% 0.22/0.43    inference(resolution,[],[f116,f84])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    r1_tarski(sK1,sK0) | ~spl2_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f82])).
% 0.22/0.43  fof(f116,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f115])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    spl2_17 | ~spl2_3 | ~spl2_4 | ~spl2_9 | ~spl2_15),
% 0.22/0.43    inference(avatar_split_clause,[],[f113,f101,f69,f49,f45,f115])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl2_9 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    spl2_15 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_9 | ~spl2_15)),
% 0.22/0.43    inference(forward_demodulation,[],[f112,f102])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | ~spl2_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f101])).
% 0.22/0.43  fof(f112,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_3 | ~spl2_4 | ~spl2_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f111,f46])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_4 | ~spl2_9)),
% 0.22/0.43    inference(superposition,[],[f70,f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f49])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) ) | ~spl2_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f69])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    spl2_16 | ~spl2_14 | ~spl2_15),
% 0.22/0.43    inference(avatar_split_clause,[],[f105,f101,f96,f107])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    spl2_14 <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_14 | ~spl2_15)),
% 0.22/0.43    inference(superposition,[],[f97,f102])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | ~spl2_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f96])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    spl2_15 | ~spl2_3 | ~spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f99,f65,f45,f101])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl2_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.43  fof(f99,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_8)),
% 0.22/0.43    inference(resolution,[],[f66,f46])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f65])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    spl2_14 | ~spl2_3 | ~spl2_4 | ~spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f94,f61,f49,f45,f96])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl2_7 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.22/0.43    inference(forward_demodulation,[],[f93,f50])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) ) | (~spl2_3 | ~spl2_7)),
% 0.22/0.43    inference(resolution,[],[f62,f46])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f61])).
% 0.22/0.43  fof(f92,plain,(
% 0.22/0.43    spl2_13 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f88,f57,f53,f49,f45,f90])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl2_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl2_6 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6)),
% 0.22/0.43    inference(forward_demodulation,[],[f87,f50])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.22/0.43    inference(forward_demodulation,[],[f86,f54])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_6)),
% 0.22/0.43    inference(resolution,[],[f58,f46])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl2_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f57])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    spl2_12 | ~spl2_2 | ~spl2_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f80,f77,f40,f82])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl2_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_11)),
% 0.22/0.43    inference(resolution,[],[f78,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f40])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f77])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    spl2_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f33,f77])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.43    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    spl2_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f32,f73])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : ((k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k7_relat_1(X1,X0) = k7_relat_1(X2,X0) => k9_relat_1(X1,X0) = k9_relat_1(X2,X0))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f69])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f30,f65])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f29,f61])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f28,f57])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f49])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f45])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f40])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.43    inference(negated_conjecture,[],[f9])).
% 0.22/0.43  fof(f9,conjecture,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f35])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f22])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (8004)------------------------------
% 0.22/0.43  % (8004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (8004)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (8004)Memory used [KB]: 6140
% 0.22/0.43  % (8004)Time elapsed: 0.008 s
% 0.22/0.43  % (8004)------------------------------
% 0.22/0.43  % (8004)------------------------------
% 0.22/0.44  % (7993)Success in time 0.076 s
%------------------------------------------------------------------------------
