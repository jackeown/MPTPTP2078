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
% DateTime   : Thu Dec  3 12:44:54 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  118 (1650 expanded)
%              Number of leaves         :   19 ( 467 expanded)
%              Depth                    :   21
%              Number of atoms          :  275 (3996 expanded)
%              Number of equality atoms :   65 (1424 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f965,f991,f1363,f1384])).

fof(f1384,plain,
    ( ~ spl4_14
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f1383,f974,f505])).

fof(f505,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f974,plain,
    ( spl4_21
  <=> sK1 = k3_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1383,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1382,f37])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f1382,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f1021,f514])).

fof(f514,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f254,f513])).

fof(f513,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f488,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f488,plain,(
    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f59,f254])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f41,f41])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f254,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(unit_resulting_resolution,[],[f174,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f174,plain,(
    r1_xboole_0(k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f136])).

fof(f136,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,sK2)
      | ~ r1_tarski(X1,k5_xboole_0(sK0,sK2)) ) ),
    inference(forward_demodulation,[],[f101,f113])).

fof(f113,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f72,f112])).

fof(f112,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f97,f87])).

fof(f87,plain,(
    sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f82,f71])).

fof(f71,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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
    inference(definition_unfolding,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f73,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f97,plain,(
    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f59,f72])).

fof(f72,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f61])).

fof(f101,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1021,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f1016,f514])).

fof(f1016,plain,
    ( ~ m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1))
    | sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_21 ),
    inference(superposition,[],[f993,f513])).

fof(f993,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
        | sK1 = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) )
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f418,f976])).

fof(f976,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f974])).

fof(f418,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
      | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1)
      | ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f49,f212])).

fof(f212,plain,(
    ! [X2] :
      ( sK1 = k3_subset_1(sK1,k5_xboole_0(X2,k3_xboole_0(X2,sK2)))
      | ~ m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f91,f61])).

fof(f91,plain,(
    ! [X0] : sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f69,f63])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f35,f64])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1363,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1362])).

fof(f1362,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1356,f38])).

fof(f1356,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f1041,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1041,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f507,f1031,f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1031,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f255,f507,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f255,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f174,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f507,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f505])).

fof(f991,plain,
    ( spl4_21
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f420,f226,f974])).

fof(f226,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f420,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK1 = k3_subset_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f419,f224])).

fof(f224,plain,(
    sK1 = k5_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f222,f178])).

fof(f178,plain,(
    r1_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f124,f159])).

fof(f159,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | ~ r1_xboole_0(X0,k5_xboole_0(sK0,sK2)) ) ),
    inference(superposition,[],[f117,f63])).

fof(f117,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2)))) ),
    inference(backward_demodulation,[],[f76,f113])).

fof(f76,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f36,f64])).

fof(f36,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f124,plain,(
    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f96,f113])).

fof(f96,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f69,f72])).

fof(f222,plain,
    ( sK1 = k5_xboole_0(sK1,sK1)
    | ~ r1_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f221,f63])).

fof(f221,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f91,f214])).

fof(f214,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f59,f91])).

fof(f419,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f412,f224])).

fof(f412,plain,
    ( sK1 = k3_subset_1(sK1,k5_xboole_0(sK1,sK1))
    | ~ m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f212,f211])).

fof(f211,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f91,f59])).

fof(f965,plain,
    ( ~ spl4_14
    | spl4_6 ),
    inference(avatar_split_clause,[],[f722,f226,f505])).

fof(f722,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(forward_demodulation,[],[f705,f514])).

fof(f705,plain,
    ( ~ m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(superposition,[],[f421,f513])).

fof(f421,plain,
    ( ! [X1] : ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f417,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f226])).

fof(f417,plain,(
    ! [X1] :
      ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,(
    ! [X1] :
      ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f47,f212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.51  % (18978)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (18986)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (18977)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (18976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (18994)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (19001)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (18994)Refutation not found, incomplete strategy% (18994)------------------------------
% 0.21/0.54  % (18994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18994)Memory used [KB]: 10746
% 0.21/0.54  % (18994)Time elapsed: 0.122 s
% 0.21/0.54  % (18994)------------------------------
% 0.21/0.54  % (18994)------------------------------
% 0.21/0.54  % (18995)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (18975)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (18974)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (18993)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (18982)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (18982)Refutation not found, incomplete strategy% (18982)------------------------------
% 0.21/0.55  % (18982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18982)Memory used [KB]: 10618
% 0.21/0.55  % (18982)Time elapsed: 0.131 s
% 0.21/0.55  % (18982)------------------------------
% 0.21/0.55  % (18982)------------------------------
% 0.21/0.55  % (18987)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (18985)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (18991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (18988)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (18998)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (18983)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (18984)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (18979)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (18996)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (18999)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (18990)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (18972)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (18972)Refutation not found, incomplete strategy% (18972)------------------------------
% 0.21/0.56  % (18972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18972)Memory used [KB]: 1663
% 0.21/0.56  % (18972)Time elapsed: 0.112 s
% 0.21/0.56  % (18972)------------------------------
% 0.21/0.56  % (18972)------------------------------
% 0.21/0.56  % (18989)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (19000)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (18980)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.62/0.57  % (18992)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.62/0.58  % (18989)Refutation not found, incomplete strategy% (18989)------------------------------
% 1.62/0.58  % (18989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (18989)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (18989)Memory used [KB]: 10618
% 1.62/0.58  % (18989)Time elapsed: 0.167 s
% 1.62/0.58  % (18989)------------------------------
% 1.62/0.58  % (18989)------------------------------
% 1.62/0.59  % (18992)Refutation not found, incomplete strategy% (18992)------------------------------
% 1.62/0.59  % (18992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (18992)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (18992)Memory used [KB]: 10874
% 1.62/0.59  % (18992)Time elapsed: 0.170 s
% 1.62/0.59  % (18992)------------------------------
% 1.62/0.59  % (18992)------------------------------
% 1.78/0.60  % (18981)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.78/0.60  % (18981)Refutation not found, incomplete strategy% (18981)------------------------------
% 1.78/0.60  % (18981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (18981)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (18981)Memory used [KB]: 10618
% 1.78/0.60  % (18981)Time elapsed: 0.167 s
% 1.78/0.60  % (18981)------------------------------
% 1.78/0.60  % (18981)------------------------------
% 1.78/0.61  % (18997)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.78/0.62  % (18973)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.59/0.71  % (19005)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.59/0.72  % (19007)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.59/0.72  % (18998)Refutation found. Thanks to Tanya!
% 2.59/0.72  % SZS status Theorem for theBenchmark
% 2.59/0.72  % SZS output start Proof for theBenchmark
% 2.59/0.72  fof(f1388,plain,(
% 2.59/0.72    $false),
% 2.59/0.72    inference(avatar_sat_refutation,[],[f965,f991,f1363,f1384])).
% 2.59/0.72  fof(f1384,plain,(
% 2.59/0.72    ~spl4_14 | ~spl4_21),
% 2.59/0.72    inference(avatar_split_clause,[],[f1383,f974,f505])).
% 2.59/0.72  fof(f505,plain,(
% 2.59/0.72    spl4_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.59/0.72  fof(f974,plain,(
% 2.59/0.72    spl4_21 <=> sK1 = k3_subset_1(sK1,sK1)),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.59/0.72  fof(f1383,plain,(
% 2.59/0.72    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl4_21),
% 2.59/0.72    inference(subsumption_resolution,[],[f1382,f37])).
% 2.59/0.72  fof(f37,plain,(
% 2.59/0.72    k1_xboole_0 != sK1),
% 2.59/0.72    inference(cnf_transformation,[],[f27])).
% 2.59/0.72  fof(f27,plain,(
% 2.59/0.72    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.59/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).
% 2.59/0.72  fof(f26,plain,(
% 2.59/0.72    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.59/0.72    introduced(choice_axiom,[])).
% 2.59/0.72  fof(f17,plain,(
% 2.59/0.72    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(flattening,[],[f16])).
% 2.59/0.72  fof(f16,plain,(
% 2.59/0.72    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f15])).
% 2.59/0.72  fof(f15,negated_conjecture,(
% 2.59/0.72    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.59/0.72    inference(negated_conjecture,[],[f14])).
% 2.59/0.72  fof(f14,conjecture,(
% 2.59/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 2.59/0.72  fof(f1382,plain,(
% 2.59/0.72    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl4_21),
% 2.59/0.72    inference(forward_demodulation,[],[f1021,f514])).
% 2.59/0.72  fof(f514,plain,(
% 2.59/0.72    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.59/0.72    inference(backward_demodulation,[],[f254,f513])).
% 2.59/0.74  fof(f513,plain,(
% 2.59/0.74    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 2.59/0.74    inference(forward_demodulation,[],[f488,f60])).
% 2.59/0.74  fof(f60,plain,(
% 2.59/0.74    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.59/0.74    inference(definition_unfolding,[],[f39,f41])).
% 2.59/0.74  fof(f41,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f1])).
% 2.59/0.74  fof(f1,axiom,(
% 2.59/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.59/0.74  fof(f39,plain,(
% 2.59/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.59/0.74    inference(cnf_transformation,[],[f4])).
% 2.59/0.74  fof(f4,axiom,(
% 2.59/0.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.59/0.74  fof(f488,plain,(
% 2.59/0.74    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 2.59/0.74    inference(superposition,[],[f59,f254])).
% 2.59/0.74  fof(f59,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f40,f41,f41])).
% 2.59/0.74  fof(f40,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f5])).
% 2.59/0.74  fof(f5,axiom,(
% 2.59/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.59/0.74  fof(f254,plain,(
% 2.59/0.74    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2))),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f174,f63])).
% 2.59/0.74  fof(f63,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f50,f41])).
% 2.59/0.74  fof(f50,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f29])).
% 2.59/0.74  fof(f29,plain,(
% 2.59/0.74    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.59/0.74    inference(nnf_transformation,[],[f7])).
% 2.59/0.74  fof(f7,axiom,(
% 2.59/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.59/0.74  fof(f174,plain,(
% 2.59/0.74    r1_xboole_0(k1_xboole_0,sK2)),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f38,f136])).
% 2.59/0.74  fof(f136,plain,(
% 2.59/0.74    ( ! [X1] : (r1_xboole_0(X1,sK2) | ~r1_tarski(X1,k5_xboole_0(sK0,sK2))) )),
% 2.59/0.74    inference(forward_demodulation,[],[f101,f113])).
% 2.59/0.74  fof(f113,plain,(
% 2.59/0.74    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 2.59/0.74    inference(backward_demodulation,[],[f72,f112])).
% 2.59/0.74  fof(f112,plain,(
% 2.59/0.74    sK2 = k3_xboole_0(sK0,sK2)),
% 2.59/0.74    inference(forward_demodulation,[],[f97,f87])).
% 2.59/0.74  fof(f87,plain,(
% 2.59/0.74    sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))),
% 2.59/0.74    inference(forward_demodulation,[],[f82,f71])).
% 2.59/0.74  fof(f71,plain,(
% 2.59/0.74    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f34,f49])).
% 2.59/0.74  fof(f49,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f23])).
% 2.59/0.74  fof(f23,plain,(
% 2.59/0.74    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.74    inference(ennf_transformation,[],[f13])).
% 2.59/0.74  fof(f13,axiom,(
% 2.59/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.59/0.74  fof(f34,plain,(
% 2.59/0.74    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.59/0.74    inference(cnf_transformation,[],[f27])).
% 2.59/0.74  fof(f82,plain,(
% 2.59/0.74    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f73,f61])).
% 2.59/0.74  fof(f61,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f48,f41])).
% 2.59/0.74  fof(f48,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f22])).
% 2.59/0.74  fof(f22,plain,(
% 2.59/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.74    inference(ennf_transformation,[],[f11])).
% 2.59/0.74  fof(f11,axiom,(
% 2.59/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.59/0.74  fof(f73,plain,(
% 2.59/0.74    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f34,f47])).
% 2.59/0.74  fof(f47,plain,(
% 2.59/0.74    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f21])).
% 2.59/0.74  fof(f21,plain,(
% 2.59/0.74    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.74    inference(ennf_transformation,[],[f12])).
% 2.59/0.74  fof(f12,axiom,(
% 2.59/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.59/0.74  fof(f97,plain,(
% 2.59/0.74    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))),
% 2.59/0.74    inference(superposition,[],[f59,f72])).
% 2.59/0.74  fof(f72,plain,(
% 2.59/0.74    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f34,f61])).
% 2.59/0.74  fof(f101,plain,(
% 2.59/0.74    ( ! [X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK2)) | r1_xboole_0(X1,sK2)) )),
% 2.59/0.74    inference(superposition,[],[f65,f72])).
% 2.59/0.74  fof(f65,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f58,f41])).
% 2.59/0.74  fof(f58,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f25])).
% 2.59/0.74  fof(f25,plain,(
% 2.59/0.74    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.59/0.74    inference(ennf_transformation,[],[f2])).
% 2.59/0.74  fof(f2,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.59/0.74  fof(f38,plain,(
% 2.59/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f3])).
% 2.59/0.74  fof(f3,axiom,(
% 2.59/0.74    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.59/0.74  fof(f1021,plain,(
% 2.59/0.74    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_21),
% 2.59/0.74    inference(forward_demodulation,[],[f1016,f514])).
% 2.59/0.74  fof(f1016,plain,(
% 2.59/0.74    ~m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1)) | sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_21),
% 2.59/0.74    inference(superposition,[],[f993,f513])).
% 2.59/0.74  fof(f993,plain,(
% 2.59/0.74    ( ! [X0] : (~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | sK1 = k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ) | ~spl4_21),
% 2.59/0.74    inference(backward_demodulation,[],[f418,f976])).
% 2.59/0.74  fof(f976,plain,(
% 2.59/0.74    sK1 = k3_subset_1(sK1,sK1) | ~spl4_21),
% 2.59/0.74    inference(avatar_component_clause,[],[f974])).
% 2.59/0.74  fof(f418,plain,(
% 2.59/0.74    ( ! [X0] : (~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1)) )),
% 2.59/0.74    inference(duplicate_literal_removal,[],[f415])).
% 2.59/0.74  fof(f415,plain,(
% 2.59/0.74    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1) | ~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))) )),
% 2.59/0.74    inference(superposition,[],[f49,f212])).
% 2.59/0.74  fof(f212,plain,(
% 2.59/0.74    ( ! [X2] : (sK1 = k3_subset_1(sK1,k5_xboole_0(X2,k3_xboole_0(X2,sK2))) | ~m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,sK2)),k1_zfmisc_1(sK1))) )),
% 2.59/0.74    inference(superposition,[],[f91,f61])).
% 2.59/0.74  fof(f91,plain,(
% 2.59/0.74    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))))) )),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f69,f63])).
% 2.59/0.74  fof(f69,plain,(
% 2.59/0.74    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) )),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f35,f64])).
% 2.59/0.74  fof(f64,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f56,f41])).
% 2.59/0.74  fof(f56,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f24])).
% 2.59/0.74  fof(f24,plain,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.59/0.74    inference(ennf_transformation,[],[f8])).
% 2.59/0.74  fof(f8,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.59/0.74  fof(f35,plain,(
% 2.59/0.74    r1_tarski(sK1,sK2)),
% 2.59/0.74    inference(cnf_transformation,[],[f27])).
% 2.59/0.74  fof(f1363,plain,(
% 2.59/0.74    spl4_14),
% 2.59/0.74    inference(avatar_contradiction_clause,[],[f1362])).
% 2.59/0.74  fof(f1362,plain,(
% 2.59/0.74    $false | spl4_14),
% 2.59/0.74    inference(subsumption_resolution,[],[f1356,f38])).
% 2.59/0.74  fof(f1356,plain,(
% 2.59/0.74    ~r1_tarski(k1_xboole_0,sK1) | spl4_14),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f1041,f67])).
% 2.59/0.74  fof(f67,plain,(
% 2.59/0.74    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.59/0.74    inference(equality_resolution,[],[f53])).
% 2.59/0.74  fof(f53,plain,(
% 2.59/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.59/0.74    inference(cnf_transformation,[],[f33])).
% 2.59/0.74  fof(f33,plain,(
% 2.59/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.59/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.59/0.74  fof(f32,plain,(
% 2.59/0.74    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.59/0.74    introduced(choice_axiom,[])).
% 2.59/0.74  fof(f31,plain,(
% 2.59/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.59/0.74    inference(rectify,[],[f30])).
% 2.59/0.74  fof(f30,plain,(
% 2.59/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.59/0.74    inference(nnf_transformation,[],[f9])).
% 2.59/0.74  fof(f9,axiom,(
% 2.59/0.74    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.59/0.74  fof(f1041,plain,(
% 2.59/0.74    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_14),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f507,f1031,f43])).
% 2.59/0.74  fof(f43,plain,(
% 2.59/0.74    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f28])).
% 2.59/0.74  fof(f28,plain,(
% 2.59/0.74    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.59/0.74    inference(nnf_transformation,[],[f18])).
% 2.59/0.74  fof(f18,plain,(
% 2.59/0.74    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.59/0.74    inference(ennf_transformation,[],[f10])).
% 2.59/0.74  fof(f10,axiom,(
% 2.59/0.74    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.59/0.74  fof(f1031,plain,(
% 2.59/0.74    ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl4_14),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f255,f507,f45])).
% 2.59/0.74  fof(f45,plain,(
% 2.59/0.74    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f28])).
% 2.59/0.74  fof(f255,plain,(
% 2.59/0.74    v1_xboole_0(k1_xboole_0)),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f38,f174,f46])).
% 2.59/0.74  fof(f46,plain,(
% 2.59/0.74    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f20])).
% 2.59/0.74  fof(f20,plain,(
% 2.59/0.74    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.59/0.74    inference(flattening,[],[f19])).
% 2.59/0.74  fof(f19,plain,(
% 2.59/0.74    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.59/0.74    inference(ennf_transformation,[],[f6])).
% 2.59/0.74  fof(f6,axiom,(
% 2.59/0.74    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.59/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.59/0.74  fof(f507,plain,(
% 2.59/0.74    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_14),
% 2.59/0.74    inference(avatar_component_clause,[],[f505])).
% 2.59/0.74  fof(f991,plain,(
% 2.59/0.74    spl4_21 | ~spl4_6),
% 2.59/0.74    inference(avatar_split_clause,[],[f420,f226,f974])).
% 2.59/0.74  fof(f226,plain,(
% 2.59/0.74    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.59/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.59/0.74  fof(f420,plain,(
% 2.59/0.74    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK1 = k3_subset_1(sK1,sK1)),
% 2.59/0.74    inference(forward_demodulation,[],[f419,f224])).
% 2.59/0.74  fof(f224,plain,(
% 2.59/0.74    sK1 = k5_xboole_0(sK1,sK1)),
% 2.59/0.74    inference(subsumption_resolution,[],[f222,f178])).
% 2.59/0.74  fof(f178,plain,(
% 2.59/0.74    r1_xboole_0(sK1,sK1)),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f124,f159])).
% 2.59/0.74  fof(f159,plain,(
% 2.59/0.74    ( ! [X0] : (r1_xboole_0(sK1,X0) | ~r1_xboole_0(X0,k5_xboole_0(sK0,sK2))) )),
% 2.59/0.74    inference(superposition,[],[f117,f63])).
% 2.59/0.74  fof(f117,plain,(
% 2.59/0.74    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2))))) )),
% 2.59/0.74    inference(backward_demodulation,[],[f76,f113])).
% 2.59/0.74  fof(f76,plain,(
% 2.59/0.74    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(sK0,sK2))))) )),
% 2.59/0.74    inference(unit_resulting_resolution,[],[f36,f64])).
% 2.59/0.74  fof(f36,plain,(
% 2.59/0.74    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.59/0.74    inference(cnf_transformation,[],[f27])).
% 2.59/0.74  fof(f124,plain,(
% 2.59/0.74    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 2.59/0.74    inference(backward_demodulation,[],[f96,f113])).
% 2.59/0.74  fof(f96,plain,(
% 2.59/0.74    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.59/0.74    inference(superposition,[],[f69,f72])).
% 2.59/0.74  fof(f222,plain,(
% 2.59/0.74    sK1 = k5_xboole_0(sK1,sK1) | ~r1_xboole_0(sK1,sK1)),
% 2.59/0.74    inference(superposition,[],[f221,f63])).
% 2.59/0.74  fof(f221,plain,(
% 2.59/0.74    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 2.59/0.74    inference(backward_demodulation,[],[f91,f214])).
% 2.59/0.74  fof(f214,plain,(
% 2.59/0.74    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) )),
% 2.59/0.74    inference(superposition,[],[f59,f91])).
% 2.59/0.74  fof(f419,plain,(
% 2.59/0.74    sK1 = k3_subset_1(sK1,sK1) | ~m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 2.59/0.74    inference(forward_demodulation,[],[f412,f224])).
% 2.59/0.74  fof(f412,plain,(
% 2.59/0.74    sK1 = k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) | ~m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 2.59/0.74    inference(superposition,[],[f212,f211])).
% 2.59/0.74  fof(f211,plain,(
% 2.59/0.74    sK1 = k3_xboole_0(sK1,sK2)),
% 2.59/0.74    inference(superposition,[],[f91,f59])).
% 2.59/0.74  fof(f965,plain,(
% 2.59/0.74    ~spl4_14 | spl4_6),
% 2.59/0.74    inference(avatar_split_clause,[],[f722,f226,f505])).
% 2.59/0.74  fof(f722,plain,(
% 2.59/0.74    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_6),
% 2.59/0.74    inference(forward_demodulation,[],[f705,f514])).
% 2.59/0.74  fof(f705,plain,(
% 2.59/0.74    ~m1_subset_1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK1)) | spl4_6),
% 2.59/0.74    inference(superposition,[],[f421,f513])).
% 2.59/0.74  fof(f421,plain,(
% 2.59/0.74    ( ! [X1] : (~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))) ) | spl4_6),
% 2.59/0.74    inference(subsumption_resolution,[],[f417,f228])).
% 2.59/0.74  fof(f228,plain,(
% 2.59/0.74    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_6),
% 2.59/0.74    inference(avatar_component_clause,[],[f226])).
% 2.59/0.74  fof(f417,plain,(
% 2.59/0.74    ( ! [X1] : (m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))) )),
% 2.59/0.74    inference(duplicate_literal_removal,[],[f416])).
% 2.59/0.74  fof(f416,plain,(
% 2.59/0.74    ( ! [X1] : (m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,sK2)),k1_zfmisc_1(sK1))) )),
% 2.59/0.74    inference(superposition,[],[f47,f212])).
% 2.59/0.74  % SZS output end Proof for theBenchmark
% 2.59/0.74  % (18998)------------------------------
% 2.59/0.74  % (18998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.74  % (18998)Termination reason: Refutation
% 2.59/0.74  
% 2.59/0.74  % (18998)Memory used [KB]: 11385
% 2.59/0.74  % (18998)Time elapsed: 0.315 s
% 2.59/0.74  % (18998)------------------------------
% 2.59/0.74  % (18998)------------------------------
% 2.59/0.75  % (18971)Success in time 0.382 s
%------------------------------------------------------------------------------
