%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 151 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  214 ( 360 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f854,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f57,f67,f71,f77,f82,f90,f121,f146,f158,f181,f336,f791,f852])).

fof(f852,plain,
    ( spl2_18
    | ~ spl2_30
    | ~ spl2_76 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | spl2_18
    | ~ spl2_30
    | ~ spl2_76 ),
    inference(subsumption_resolution,[],[f335,f829])).

fof(f829,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | spl2_18
    | ~ spl2_76 ),
    inference(superposition,[],[f145,f790])).

fof(f790,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f789])).

fof(f789,plain,
    ( spl2_76
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f145,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_18
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f335,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl2_30
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f791,plain,
    ( spl2_76
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f184,f179,f65,f789])).

fof(f65,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f179,plain,
    ( spl2_22
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f184,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(superposition,[],[f180,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f180,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f179])).

fof(f336,plain,
    ( spl2_30
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f171,f155,f47,f333])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f155,plain,
    ( spl2_20
  <=> k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f171,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(superposition,[],[f48,f157])).

fof(f157,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f48,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f181,plain,
    ( spl2_22
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f72,f65,f55,f179])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f72,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f66,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f158,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f88,f37,f32,f155])).

fof(f32,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f37,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f34,f39,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f34,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f146,plain,
    ( ~ spl2_18
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_12
    | spl2_14 ),
    inference(avatar_split_clause,[],[f123,f118,f88,f80,f69,f37,f143])).

fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f80,plain,
    ( spl2_11
  <=> ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f118,plain,
    ( spl2_14
  <=> r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f123,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_12
    | spl2_14 ),
    inference(forward_demodulation,[],[f122,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f122,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_12
    | spl2_14 ),
    inference(forward_demodulation,[],[f120,f101])).

fof(f101,plain,
    ( ! [X0] : k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,X0)))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f39,f81,f89])).

fof(f81,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f120,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,sK1))))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( ~ spl2_14
    | spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f83,f75,f42,f118])).

fof(f42,plain,
    ( spl2_3
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f75,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f83,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,sK1))))
    | spl2_3
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f44,f76])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f44,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f21,f88])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f82,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f62,f51,f32,f80])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f62,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f34,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f75])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f67,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f45,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f30,f42])).

fof(f30,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f20,f24])).

fof(f20,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:36:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (10916)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (10916)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f854,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f57,f67,f71,f77,f82,f90,f121,f146,f158,f181,f336,f791,f852])).
% 0.22/0.47  fof(f852,plain,(
% 0.22/0.47    spl2_18 | ~spl2_30 | ~spl2_76),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f851])).
% 0.22/0.47  fof(f851,plain,(
% 0.22/0.47    $false | (spl2_18 | ~spl2_30 | ~spl2_76)),
% 0.22/0.47    inference(subsumption_resolution,[],[f335,f829])).
% 0.22/0.47  fof(f829,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | (spl2_18 | ~spl2_76)),
% 0.22/0.47    inference(superposition,[],[f145,f790])).
% 0.22/0.47  fof(f790,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | ~spl2_76),
% 0.22/0.47    inference(avatar_component_clause,[],[f789])).
% 0.22/0.47  fof(f789,plain,(
% 0.22/0.47    spl2_76 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) | spl2_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f143])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    spl2_18 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.47  fof(f335,plain,(
% 0.22/0.47    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | ~spl2_30),
% 0.22/0.47    inference(avatar_component_clause,[],[f333])).
% 0.22/0.47  fof(f333,plain,(
% 0.22/0.47    spl2_30 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.47  fof(f791,plain,(
% 0.22/0.47    spl2_76 | ~spl2_8 | ~spl2_22),
% 0.22/0.47    inference(avatar_split_clause,[],[f184,f179,f65,f789])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.47  fof(f179,plain,(
% 0.22/0.47    spl2_22 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.47  fof(f184,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl2_8 | ~spl2_22)),
% 0.22/0.47    inference(superposition,[],[f180,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl2_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f180,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | ~spl2_22),
% 0.22/0.47    inference(avatar_component_clause,[],[f179])).
% 0.22/0.47  fof(f336,plain,(
% 0.22/0.47    spl2_30 | ~spl2_4 | ~spl2_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f171,f155,f47,f333])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    spl2_20 <=> k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | (~spl2_4 | ~spl2_20)),
% 0.22/0.47    inference(superposition,[],[f48,f157])).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f155])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    spl2_22 | ~spl2_6 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f72,f65,f55,f179])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl2_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | (~spl2_6 | ~spl2_8)),
% 0.22/0.47    inference(superposition,[],[f66,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f55])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    spl2_20 | ~spl2_1 | ~spl2_2 | ~spl2_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f93,f88,f37,f32,f155])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl2_12 <=> ! [X1,X0] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_12)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f34,f39,f89])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f37])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    v1_relat_1(sK0) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    ~spl2_18 | ~spl2_2 | ~spl2_9 | ~spl2_11 | ~spl2_12 | spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f123,f118,f88,f80,f69,f37,f143])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl2_11 <=> ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    spl2_14 <=> r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,sK1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) | (~spl2_2 | ~spl2_9 | ~spl2_11 | ~spl2_12 | spl2_14)),
% 0.22/0.47    inference(forward_demodulation,[],[f122,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl2_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f69])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) | (~spl2_2 | ~spl2_11 | ~spl2_12 | spl2_14)),
% 0.22/0.47    inference(forward_demodulation,[],[f120,f101])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,X0)))) ) | (~spl2_2 | ~spl2_11 | ~spl2_12)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f39,f81,f89])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,sK1)))) | spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f118])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ~spl2_14 | spl2_3 | ~spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f83,f75,f42,f118])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl2_3 <=> r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,sK1)))) | (spl2_3 | ~spl2_10)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f44,f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl2_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f75])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) | spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl2_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f88])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl2_11 | ~spl2_1 | ~spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f62,f51,f32,f80])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_5)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f34,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f75])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f69])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f65])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f27,f51])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f47])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f30,f42])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    inference(forward_demodulation,[],[f29,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.22/0.48    inference(forward_demodulation,[],[f20,f24])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f32])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (10916)------------------------------
% 0.22/0.48  % (10916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10916)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (10916)Memory used [KB]: 6908
% 0.22/0.48  % (10916)Time elapsed: 0.042 s
% 0.22/0.48  % (10916)------------------------------
% 0.22/0.48  % (10916)------------------------------
% 0.22/0.48  % (10911)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (10907)Success in time 0.114 s
%------------------------------------------------------------------------------
