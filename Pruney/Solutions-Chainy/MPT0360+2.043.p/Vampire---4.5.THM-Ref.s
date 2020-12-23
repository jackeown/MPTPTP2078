%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:54 EST 2020

% Result     : Theorem 2.64s
% Output     : Refutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  121 (1576 expanded)
%              Number of leaves         :   20 ( 447 expanded)
%              Depth                    :   20
%              Number of atoms          :  283 (3813 expanded)
%              Number of equality atoms :   67 (1355 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1024,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f972,f983,f985,f1009,f1023])).

fof(f1023,plain,
    ( ~ spl4_20
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f1022])).

fof(f1022,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1021,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f1021,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f994,f979])).

fof(f979,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f977])).

fof(f977,plain,
    ( spl4_20
  <=> k1_xboole_0 = k3_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f994,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f992])).

fof(f992,plain,
    ( spl4_21
  <=> sK1 = k3_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1009,plain,
    ( spl4_21
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f421,f229,f992])).

fof(f229,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f421,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK1 = k3_subset_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f420,f227])).

fof(f227,plain,(
    sK1 = k5_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f225,f182])).

fof(f182,plain,(
    r1_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f125,f160])).

fof(f160,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | ~ r1_xboole_0(X0,k5_xboole_0(sK0,sK2)) ) ),
    inference(superposition,[],[f118,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f118,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2)))) ),
    inference(backward_demodulation,[],[f76,f114])).

fof(f114,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f72,f113])).

fof(f113,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f98,f87])).

fof(f87,plain,(
    sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f82,f71])).

fof(f71,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f73,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f98,plain,(
    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f59,f72])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f41,f41])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f72,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f61])).

fof(f76,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f36,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f41])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f36,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,(
    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f97,f114])).

fof(f97,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f69,f72])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f35,f64])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f225,plain,
    ( sK1 = k5_xboole_0(sK1,sK1)
    | ~ r1_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f224,f63])).

fof(f224,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f92,f217])).

fof(f217,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f59,f92])).

fof(f92,plain,(
    ! [X0] : sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f69,f63])).

fof(f420,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f413,f227])).

fof(f413,plain,
    ( sK1 = k3_subset_1(sK1,k5_xboole_0(sK1,sK1))
    | ~ m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f215,f214])).

fof(f214,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f92,f59])).

fof(f215,plain,(
    ! [X2] :
      ( sK1 = k3_subset_1(sK1,k5_xboole_0(X2,k3_xboole_0(X2,sK2)))
      | ~ m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f92,f61])).

fof(f985,plain,
    ( ~ spl4_14
    | spl4_20 ),
    inference(avatar_split_clause,[],[f984,f977,f498])).

fof(f498,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f984,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f691,f507])).

fof(f507,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f254,f506])).

fof(f506,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f481,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f481,plain,(
    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f59,f254])).

fof(f254,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(unit_resulting_resolution,[],[f178,f63])).

fof(f178,plain,(
    r1_xboole_0(k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f137])).

fof(f137,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,sK2)
      | ~ r1_tarski(X1,k5_xboole_0(sK0,sK2)) ) ),
    inference(forward_demodulation,[],[f102,f114])).

fof(f102,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(X1,sK2) ) ),
    inference(superposition,[],[f65,f72])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f691,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f674,f507])).

fof(f674,plain,
    ( ~ m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f419,f506])).

fof(f419,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
      | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1)
      | ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f48,f215])).

fof(f983,plain,
    ( ~ spl4_14
    | spl4_6 ),
    inference(avatar_split_clause,[],[f692,f229,f498])).

fof(f692,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(forward_demodulation,[],[f675,f507])).

fof(f675,plain,
    ( ~ m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(superposition,[],[f422,f506])).

fof(f422,plain,
    ( ! [X1] : ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f418,f231])).

fof(f231,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f229])).

fof(f418,plain,(
    ! [X1] :
      ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,(
    ! [X1] :
      ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f46,f215])).

fof(f972,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f965,f38])).

fof(f965,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f708,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f708,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f500,f651,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f651,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f91,f500,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f38,f69,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f500,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:45:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (18740)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (18732)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18724)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (18723)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (18739)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (18731)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (18739)Refutation not found, incomplete strategy% (18739)------------------------------
% 0.22/0.59  % (18739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (18737)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.60  % (18739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (18739)Memory used [KB]: 10746
% 0.22/0.60  % (18739)Time elapsed: 0.156 s
% 0.22/0.60  % (18739)------------------------------
% 0.22/0.60  % (18739)------------------------------
% 0.22/0.60  % (18727)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  % (18717)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.61  % (18745)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.61  % (18717)Refutation not found, incomplete strategy% (18717)------------------------------
% 0.22/0.61  % (18717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (18717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (18717)Memory used [KB]: 1663
% 0.22/0.61  % (18717)Time elapsed: 0.173 s
% 0.22/0.61  % (18717)------------------------------
% 0.22/0.61  % (18717)------------------------------
% 0.22/0.61  % (18746)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.61  % (18727)Refutation not found, incomplete strategy% (18727)------------------------------
% 0.22/0.61  % (18727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (18727)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (18727)Memory used [KB]: 10618
% 0.22/0.61  % (18727)Time elapsed: 0.174 s
% 0.22/0.61  % (18727)------------------------------
% 0.22/0.61  % (18727)------------------------------
% 0.22/0.61  % (18720)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.61  % (18722)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.61  % (18721)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.94/0.62  % (18728)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.94/0.62  % (18730)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.94/0.62  % (18735)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.94/0.62  % (18725)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.94/0.62  % (18726)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.94/0.62  % (18729)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.94/0.62  % (18738)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.94/0.62  % (18719)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.94/0.62  % (18726)Refutation not found, incomplete strategy% (18726)------------------------------
% 1.94/0.62  % (18726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.62  % (18726)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.62  
% 1.94/0.62  % (18726)Memory used [KB]: 10618
% 1.94/0.62  % (18726)Time elapsed: 0.186 s
% 1.94/0.62  % (18726)------------------------------
% 1.94/0.62  % (18726)------------------------------
% 1.94/0.62  % (18744)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.94/0.63  % (18733)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.94/0.63  % (18741)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.94/0.63  % (18737)Refutation not found, incomplete strategy% (18737)------------------------------
% 1.94/0.63  % (18737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (18743)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.02/0.63  % (18718)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.02/0.64  % (18736)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.02/0.64  % (18734)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.02/0.65  % (18737)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.65  
% 2.02/0.65  % (18737)Memory used [KB]: 10874
% 2.02/0.65  % (18737)Time elapsed: 0.195 s
% 2.02/0.65  % (18737)------------------------------
% 2.02/0.65  % (18737)------------------------------
% 2.02/0.65  % (18742)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.19/0.65  % (18734)Refutation not found, incomplete strategy% (18734)------------------------------
% 2.19/0.65  % (18734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (18734)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (18734)Memory used [KB]: 10618
% 2.19/0.67  % (18734)Time elapsed: 0.221 s
% 2.19/0.67  % (18734)------------------------------
% 2.19/0.67  % (18734)------------------------------
% 2.64/0.74  % (18743)Refutation found. Thanks to Tanya!
% 2.64/0.74  % SZS status Theorem for theBenchmark
% 2.64/0.77  % SZS output start Proof for theBenchmark
% 2.64/0.77  fof(f1024,plain,(
% 2.64/0.77    $false),
% 2.64/0.77    inference(avatar_sat_refutation,[],[f972,f983,f985,f1009,f1023])).
% 2.64/0.77  fof(f1023,plain,(
% 2.64/0.77    ~spl4_20 | ~spl4_21),
% 2.64/0.77    inference(avatar_contradiction_clause,[],[f1022])).
% 2.64/0.77  fof(f1022,plain,(
% 2.64/0.77    $false | (~spl4_20 | ~spl4_21)),
% 2.64/0.77    inference(subsumption_resolution,[],[f1021,f37])).
% 2.64/0.77  fof(f37,plain,(
% 2.64/0.77    k1_xboole_0 != sK1),
% 2.64/0.77    inference(cnf_transformation,[],[f27])).
% 2.64/0.77  fof(f27,plain,(
% 2.64/0.77    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.64/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).
% 2.64/0.77  fof(f26,plain,(
% 2.64/0.77    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.64/0.77    introduced(choice_axiom,[])).
% 2.64/0.77  fof(f17,plain,(
% 2.64/0.77    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.64/0.77    inference(flattening,[],[f16])).
% 2.64/0.77  fof(f16,plain,(
% 2.64/0.77    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.64/0.77    inference(ennf_transformation,[],[f15])).
% 2.64/0.77  fof(f15,negated_conjecture,(
% 2.64/0.77    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.64/0.77    inference(negated_conjecture,[],[f14])).
% 2.64/0.77  fof(f14,conjecture,(
% 2.64/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.64/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 2.64/0.77  fof(f1021,plain,(
% 2.64/0.77    k1_xboole_0 = sK1 | (~spl4_20 | ~spl4_21)),
% 2.64/0.77    inference(forward_demodulation,[],[f994,f979])).
% 2.64/0.77  fof(f979,plain,(
% 2.64/0.77    k1_xboole_0 = k3_subset_1(sK1,sK1) | ~spl4_20),
% 2.64/0.77    inference(avatar_component_clause,[],[f977])).
% 2.64/0.77  fof(f977,plain,(
% 2.64/0.77    spl4_20 <=> k1_xboole_0 = k3_subset_1(sK1,sK1)),
% 2.64/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.64/0.77  fof(f994,plain,(
% 2.64/0.77    sK1 = k3_subset_1(sK1,sK1) | ~spl4_21),
% 2.64/0.77    inference(avatar_component_clause,[],[f992])).
% 2.64/0.77  fof(f992,plain,(
% 2.64/0.77    spl4_21 <=> sK1 = k3_subset_1(sK1,sK1)),
% 2.64/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.64/0.77  fof(f1009,plain,(
% 2.64/0.77    spl4_21 | ~spl4_6),
% 2.64/0.77    inference(avatar_split_clause,[],[f421,f229,f992])).
% 2.64/0.77  fof(f229,plain,(
% 2.64/0.77    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.64/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.64/0.77  fof(f421,plain,(
% 2.64/0.77    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK1 = k3_subset_1(sK1,sK1)),
% 2.64/0.77    inference(forward_demodulation,[],[f420,f227])).
% 2.64/0.77  fof(f227,plain,(
% 2.64/0.77    sK1 = k5_xboole_0(sK1,sK1)),
% 2.64/0.77    inference(subsumption_resolution,[],[f225,f182])).
% 2.64/0.77  fof(f182,plain,(
% 2.64/0.77    r1_xboole_0(sK1,sK1)),
% 2.64/0.77    inference(unit_resulting_resolution,[],[f125,f160])).
% 2.94/0.77  fof(f160,plain,(
% 2.94/0.77    ( ! [X0] : (r1_xboole_0(sK1,X0) | ~r1_xboole_0(X0,k5_xboole_0(sK0,sK2))) )),
% 2.94/0.77    inference(superposition,[],[f118,f63])).
% 2.94/0.77  fof(f63,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.94/0.77    inference(definition_unfolding,[],[f49,f41])).
% 2.94/0.77  fof(f41,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f1])).
% 2.94/0.77  fof(f1,axiom,(
% 2.94/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.94/0.77  fof(f49,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f29])).
% 2.94/0.77  fof(f29,plain,(
% 2.94/0.77    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.94/0.77    inference(nnf_transformation,[],[f7])).
% 2.94/0.77  fof(f7,axiom,(
% 2.94/0.77    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.94/0.77  fof(f118,plain,(
% 2.94/0.77    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2))))) )),
% 2.94/0.77    inference(backward_demodulation,[],[f76,f114])).
% 2.94/0.77  fof(f114,plain,(
% 2.94/0.77    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 2.94/0.77    inference(backward_demodulation,[],[f72,f113])).
% 2.94/0.77  fof(f113,plain,(
% 2.94/0.77    sK2 = k3_xboole_0(sK0,sK2)),
% 2.94/0.77    inference(forward_demodulation,[],[f98,f87])).
% 2.94/0.77  fof(f87,plain,(
% 2.94/0.77    sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))),
% 2.94/0.77    inference(forward_demodulation,[],[f82,f71])).
% 2.94/0.77  fof(f71,plain,(
% 2.94/0.77    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f34,f48])).
% 2.94/0.77  fof(f48,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f21])).
% 2.94/0.77  fof(f21,plain,(
% 2.94/0.77    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.94/0.77    inference(ennf_transformation,[],[f13])).
% 2.94/0.77  fof(f13,axiom,(
% 2.94/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.94/0.77  fof(f34,plain,(
% 2.94/0.77    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.94/0.77    inference(cnf_transformation,[],[f27])).
% 2.94/0.77  fof(f82,plain,(
% 2.94/0.77    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f73,f61])).
% 2.94/0.77  fof(f61,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.94/0.77    inference(definition_unfolding,[],[f47,f41])).
% 2.94/0.77  fof(f47,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f20])).
% 2.94/0.77  fof(f20,plain,(
% 2.94/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.94/0.77    inference(ennf_transformation,[],[f11])).
% 2.94/0.77  fof(f11,axiom,(
% 2.94/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.94/0.77  fof(f73,plain,(
% 2.94/0.77    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f34,f46])).
% 2.94/0.77  fof(f46,plain,(
% 2.94/0.77    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f19])).
% 2.94/0.77  fof(f19,plain,(
% 2.94/0.77    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.94/0.77    inference(ennf_transformation,[],[f12])).
% 2.94/0.77  fof(f12,axiom,(
% 2.94/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.94/0.77  fof(f98,plain,(
% 2.94/0.77    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))),
% 2.94/0.77    inference(superposition,[],[f59,f72])).
% 2.94/0.77  fof(f59,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 2.94/0.77    inference(definition_unfolding,[],[f40,f41,f41])).
% 2.94/0.77  fof(f40,plain,(
% 2.94/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f5])).
% 2.94/0.77  fof(f5,axiom,(
% 2.94/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.94/0.77  fof(f72,plain,(
% 2.94/0.77    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f34,f61])).
% 2.94/0.77  fof(f76,plain,(
% 2.94/0.77    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(sK0,sK2))))) )),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f36,f64])).
% 2.94/0.77  fof(f64,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.94/0.77    inference(definition_unfolding,[],[f56,f41])).
% 2.94/0.77  fof(f56,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f24])).
% 2.94/0.77  fof(f24,plain,(
% 2.94/0.77    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.94/0.77    inference(ennf_transformation,[],[f8])).
% 2.94/0.77  fof(f8,axiom,(
% 2.94/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.94/0.77  fof(f36,plain,(
% 2.94/0.77    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.94/0.77    inference(cnf_transformation,[],[f27])).
% 2.94/0.77  fof(f125,plain,(
% 2.94/0.77    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 2.94/0.77    inference(backward_demodulation,[],[f97,f114])).
% 2.94/0.77  fof(f97,plain,(
% 2.94/0.77    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.94/0.77    inference(superposition,[],[f69,f72])).
% 2.94/0.77  fof(f69,plain,(
% 2.94/0.77    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) )),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f35,f64])).
% 2.94/0.77  fof(f35,plain,(
% 2.94/0.77    r1_tarski(sK1,sK2)),
% 2.94/0.77    inference(cnf_transformation,[],[f27])).
% 2.94/0.77  fof(f225,plain,(
% 2.94/0.77    sK1 = k5_xboole_0(sK1,sK1) | ~r1_xboole_0(sK1,sK1)),
% 2.94/0.77    inference(superposition,[],[f224,f63])).
% 2.94/0.77  fof(f224,plain,(
% 2.94/0.77    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 2.94/0.77    inference(backward_demodulation,[],[f92,f217])).
% 2.94/0.77  fof(f217,plain,(
% 2.94/0.77    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) )),
% 2.94/0.77    inference(superposition,[],[f59,f92])).
% 2.94/0.77  fof(f92,plain,(
% 2.94/0.77    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))))) )),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f69,f63])).
% 2.94/0.77  fof(f420,plain,(
% 2.94/0.77    sK1 = k3_subset_1(sK1,sK1) | ~m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 2.94/0.77    inference(forward_demodulation,[],[f413,f227])).
% 2.94/0.77  fof(f413,plain,(
% 2.94/0.77    sK1 = k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) | ~m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 2.94/0.77    inference(superposition,[],[f215,f214])).
% 2.94/0.77  fof(f214,plain,(
% 2.94/0.77    sK1 = k3_xboole_0(sK1,sK2)),
% 2.94/0.77    inference(superposition,[],[f92,f59])).
% 2.94/0.77  fof(f215,plain,(
% 2.94/0.77    ( ! [X2] : (sK1 = k3_subset_1(sK1,k5_xboole_0(X2,k3_xboole_0(X2,sK2))) | ~m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,sK2)),k1_zfmisc_1(sK1))) )),
% 2.94/0.77    inference(superposition,[],[f92,f61])).
% 2.94/0.77  fof(f985,plain,(
% 2.94/0.77    ~spl4_14 | spl4_20),
% 2.94/0.77    inference(avatar_split_clause,[],[f984,f977,f498])).
% 2.94/0.77  fof(f498,plain,(
% 2.94/0.77    spl4_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 2.94/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.94/0.77  fof(f984,plain,(
% 2.94/0.77    k1_xboole_0 = k3_subset_1(sK1,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 2.94/0.77    inference(forward_demodulation,[],[f691,f507])).
% 2.94/0.77  fof(f507,plain,(
% 2.94/0.77    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.94/0.77    inference(backward_demodulation,[],[f254,f506])).
% 2.94/0.77  fof(f506,plain,(
% 2.94/0.77    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 2.94/0.77    inference(forward_demodulation,[],[f481,f60])).
% 2.94/0.77  fof(f60,plain,(
% 2.94/0.77    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.94/0.77    inference(definition_unfolding,[],[f39,f41])).
% 2.94/0.77  fof(f39,plain,(
% 2.94/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.94/0.77    inference(cnf_transformation,[],[f4])).
% 2.94/0.77  fof(f4,axiom,(
% 2.94/0.77    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.94/0.77  fof(f481,plain,(
% 2.94/0.77    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 2.94/0.77    inference(superposition,[],[f59,f254])).
% 2.94/0.77  fof(f254,plain,(
% 2.94/0.77    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2))),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f178,f63])).
% 2.94/0.77  fof(f178,plain,(
% 2.94/0.77    r1_xboole_0(k1_xboole_0,sK2)),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f38,f137])).
% 2.94/0.77  fof(f137,plain,(
% 2.94/0.77    ( ! [X1] : (r1_xboole_0(X1,sK2) | ~r1_tarski(X1,k5_xboole_0(sK0,sK2))) )),
% 2.94/0.77    inference(forward_demodulation,[],[f102,f114])).
% 2.94/0.77  fof(f102,plain,(
% 2.94/0.77    ( ! [X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK2)) | r1_xboole_0(X1,sK2)) )),
% 2.94/0.77    inference(superposition,[],[f65,f72])).
% 2.94/0.77  fof(f65,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.94/0.77    inference(definition_unfolding,[],[f58,f41])).
% 2.94/0.77  fof(f58,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f25])).
% 2.94/0.77  fof(f25,plain,(
% 2.94/0.77    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.94/0.77    inference(ennf_transformation,[],[f2])).
% 2.94/0.77  fof(f2,axiom,(
% 2.94/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.94/0.77  fof(f38,plain,(
% 2.94/0.77    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f3])).
% 2.94/0.77  fof(f3,axiom,(
% 2.94/0.77    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.94/0.77  fof(f691,plain,(
% 2.94/0.77    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | k3_subset_1(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.94/0.77    inference(forward_demodulation,[],[f674,f507])).
% 2.94/0.77  fof(f674,plain,(
% 2.94/0.77    ~m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1)) | k3_subset_1(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.94/0.77    inference(superposition,[],[f419,f506])).
% 2.94/0.77  fof(f419,plain,(
% 2.94/0.77    ( ! [X0] : (~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1)) )),
% 2.94/0.77    inference(duplicate_literal_removal,[],[f416])).
% 2.94/0.77  fof(f416,plain,(
% 2.94/0.77    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1) | ~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))) )),
% 2.94/0.77    inference(superposition,[],[f48,f215])).
% 2.94/0.77  fof(f983,plain,(
% 2.94/0.77    ~spl4_14 | spl4_6),
% 2.94/0.77    inference(avatar_split_clause,[],[f692,f229,f498])).
% 2.94/0.77  fof(f692,plain,(
% 2.94/0.77    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_6),
% 2.94/0.77    inference(forward_demodulation,[],[f675,f507])).
% 2.94/0.77  fof(f675,plain,(
% 2.94/0.77    ~m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1)) | spl4_6),
% 2.94/0.77    inference(superposition,[],[f422,f506])).
% 2.94/0.77  fof(f422,plain,(
% 2.94/0.77    ( ! [X1] : (~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))) ) | spl4_6),
% 2.94/0.77    inference(subsumption_resolution,[],[f418,f231])).
% 2.94/0.77  fof(f231,plain,(
% 2.94/0.77    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_6),
% 2.94/0.77    inference(avatar_component_clause,[],[f229])).
% 2.94/0.77  fof(f418,plain,(
% 2.94/0.77    ( ! [X1] : (m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))) )),
% 2.94/0.77    inference(duplicate_literal_removal,[],[f417])).
% 2.94/0.77  fof(f417,plain,(
% 2.94/0.77    ( ! [X1] : (m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))) )),
% 2.94/0.77    inference(superposition,[],[f46,f215])).
% 2.94/0.77  fof(f972,plain,(
% 2.94/0.77    spl4_14),
% 2.94/0.77    inference(avatar_contradiction_clause,[],[f971])).
% 2.94/0.77  fof(f971,plain,(
% 2.94/0.77    $false | spl4_14),
% 2.94/0.77    inference(subsumption_resolution,[],[f965,f38])).
% 2.94/0.77  fof(f965,plain,(
% 2.94/0.77    ~r1_tarski(k1_xboole_0,sK1) | spl4_14),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f708,f67])).
% 2.94/0.77  fof(f67,plain,(
% 2.94/0.77    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.94/0.77    inference(equality_resolution,[],[f52])).
% 2.94/0.77  fof(f52,plain,(
% 2.94/0.77    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.94/0.77    inference(cnf_transformation,[],[f33])).
% 2.94/0.77  fof(f33,plain,(
% 2.94/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.94/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.94/0.77  fof(f32,plain,(
% 2.94/0.77    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.94/0.77    introduced(choice_axiom,[])).
% 2.94/0.77  fof(f31,plain,(
% 2.94/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.94/0.77    inference(rectify,[],[f30])).
% 2.94/0.77  fof(f30,plain,(
% 2.94/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.94/0.77    inference(nnf_transformation,[],[f9])).
% 2.94/0.77  fof(f9,axiom,(
% 2.94/0.77    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.94/0.77  fof(f708,plain,(
% 2.94/0.77    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_14),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f500,f651,f43])).
% 2.94/0.77  fof(f43,plain,(
% 2.94/0.77    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f28])).
% 2.94/0.77  fof(f28,plain,(
% 2.94/0.77    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.94/0.77    inference(nnf_transformation,[],[f18])).
% 2.94/0.77  fof(f18,plain,(
% 2.94/0.77    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.94/0.77    inference(ennf_transformation,[],[f10])).
% 2.94/0.77  fof(f10,axiom,(
% 2.94/0.77    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.94/0.77  fof(f651,plain,(
% 2.94/0.77    ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl4_14),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f91,f500,f45])).
% 2.94/0.77  fof(f45,plain,(
% 2.94/0.77    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f28])).
% 2.94/0.77  fof(f91,plain,(
% 2.94/0.77    v1_xboole_0(k1_xboole_0)),
% 2.94/0.77    inference(unit_resulting_resolution,[],[f38,f38,f69,f55])).
% 2.94/0.77  fof(f55,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f23])).
% 2.94/0.77  fof(f23,plain,(
% 2.94/0.77    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 2.94/0.77    inference(flattening,[],[f22])).
% 2.94/0.77  fof(f22,plain,(
% 2.94/0.77    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 2.94/0.77    inference(ennf_transformation,[],[f6])).
% 2.94/0.77  fof(f6,axiom,(
% 2.94/0.77    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 2.94/0.77  fof(f500,plain,(
% 2.94/0.77    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_14),
% 2.94/0.77    inference(avatar_component_clause,[],[f498])).
% 2.94/0.77  % SZS output end Proof for theBenchmark
% 2.94/0.77  % (18743)------------------------------
% 2.94/0.77  % (18743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.77  % (18743)Termination reason: Refutation
% 2.94/0.77  
% 2.94/0.77  % (18743)Memory used [KB]: 11257
% 2.94/0.77  % (18743)Time elapsed: 0.304 s
% 2.94/0.77  % (18743)------------------------------
% 2.94/0.77  % (18743)------------------------------
% 2.94/0.77  % (18716)Success in time 0.402 s
%------------------------------------------------------------------------------
