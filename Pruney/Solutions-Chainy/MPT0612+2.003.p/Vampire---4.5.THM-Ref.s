%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:36 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 143 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  216 ( 350 expanded)
%              Number of equality atoms :   44 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f72,f196,f416,f417,f422])).

fof(f422,plain,
    ( ~ spl4_3
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl4_3
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f65,f50,f119,f143])).

fof(f143,plain,(
    ! [X6,X7,X5] :
      ( v1_relat_1(k4_xboole_0(X5,k7_relat_1(X5,X7)))
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(k1_relat_1(X5),X6) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X6,X7,X5] :
      ( v1_relat_1(k4_xboole_0(X5,k7_relat_1(X5,X7)))
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(k1_relat_1(X5),X6)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f43,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f131,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f35,f40])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f119,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_11
  <=> v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f417,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_4 ),
    inference(avatar_split_clause,[],[f164,f69,f121,f117])).

fof(f121,plain,
    ( spl4_12
  <=> r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f69,plain,
    ( spl4_4
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f164,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))
    | spl4_4 ),
    inference(superposition,[],[f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f71,plain,
    ( k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f416,plain,
    ( ~ spl4_2
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl4_2
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f195,f372,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK1,X0)
        | r1_xboole_0(sK0,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f60])).

fof(f60,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f372,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f211,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f179,f48])).

% (9576)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f179,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k3_xboole_0(X5,X4))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f49,f91])).

fof(f91,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f73,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f47,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f195,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_13
  <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f196,plain,
    ( ~ spl4_13
    | ~ spl4_3
    | spl4_12 ),
    inference(avatar_split_clause,[],[f191,f121,f63,f193])).

fof(f191,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f186,f65])).

fof(f186,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | ~ v1_relat_1(sK2)
    | spl4_12 ),
    inference(superposition,[],[f123,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f145,f50])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f125,f132])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f123,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f72,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f67,f53,f69])).

fof(f53,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl4_1 ),
    inference(backward_demodulation,[],[f55,f40])).

fof(f55,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f66,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f53])).

fof(f34,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (9582)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (9574)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (9562)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (9566)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (9588)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (9580)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.58  % (9560)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.58  % (9588)Refutation not found, incomplete strategy% (9588)------------------------------
% 0.21/0.58  % (9588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (9563)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.52/0.59  % (9588)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (9588)Memory used [KB]: 1663
% 1.52/0.59  % (9588)Time elapsed: 0.157 s
% 1.52/0.59  % (9588)------------------------------
% 1.52/0.59  % (9588)------------------------------
% 1.52/0.60  % (9559)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.52/0.60  % (9565)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.60  % (9564)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.61  % (9572)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.84/0.61  % (9579)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.84/0.61  % (9580)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.61  % SZS output start Proof for theBenchmark
% 1.84/0.61  fof(f426,plain,(
% 1.84/0.61    $false),
% 1.84/0.61    inference(avatar_sat_refutation,[],[f56,f61,f66,f72,f196,f416,f417,f422])).
% 1.84/0.61  fof(f422,plain,(
% 1.84/0.61    ~spl4_3 | spl4_11),
% 1.84/0.61    inference(avatar_contradiction_clause,[],[f418])).
% 1.84/0.61  fof(f418,plain,(
% 1.84/0.61    $false | (~spl4_3 | spl4_11)),
% 1.84/0.61    inference(unit_resulting_resolution,[],[f65,f50,f119,f143])).
% 1.84/0.61  fof(f143,plain,(
% 1.84/0.61    ( ! [X6,X7,X5] : (v1_relat_1(k4_xboole_0(X5,k7_relat_1(X5,X7))) | ~v1_relat_1(X5) | ~r1_tarski(k1_relat_1(X5),X6)) )),
% 1.84/0.61    inference(duplicate_literal_removal,[],[f140])).
% 1.84/0.61  fof(f140,plain,(
% 1.84/0.61    ( ! [X6,X7,X5] : (v1_relat_1(k4_xboole_0(X5,k7_relat_1(X5,X7))) | ~v1_relat_1(X5) | ~r1_tarski(k1_relat_1(X5),X6) | ~v1_relat_1(X5)) )),
% 1.84/0.61    inference(superposition,[],[f43,f132])).
% 1.84/0.61  fof(f132,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.84/0.61    inference(forward_demodulation,[],[f131,f40])).
% 1.84/0.61  fof(f40,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f7])).
% 1.84/0.61  fof(f7,axiom,(
% 1.84/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.84/0.61  fof(f131,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.84/0.61    inference(forward_demodulation,[],[f35,f40])).
% 1.84/0.61  fof(f35,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f19])).
% 1.84/0.61  fof(f19,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.84/0.61    inference(flattening,[],[f18])).
% 1.84/0.61  fof(f18,plain,(
% 1.84/0.61    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.84/0.61    inference(ennf_transformation,[],[f12])).
% 1.84/0.61  fof(f12,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 1.84/0.61  fof(f43,plain,(
% 1.84/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f22])).
% 1.84/0.61  fof(f22,plain,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f9])).
% 1.84/0.61  fof(f9,axiom,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.84/0.61  fof(f119,plain,(
% 1.84/0.61    ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) | spl4_11),
% 1.84/0.61    inference(avatar_component_clause,[],[f117])).
% 1.84/0.61  fof(f117,plain,(
% 1.84/0.61    spl4_11 <=> v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.84/0.61  fof(f50,plain,(
% 1.84/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.61    inference(equality_resolution,[],[f37])).
% 1.84/0.61  fof(f37,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.84/0.61    inference(cnf_transformation,[],[f29])).
% 1.84/0.61  fof(f29,plain,(
% 1.84/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.61    inference(flattening,[],[f28])).
% 1.84/0.61  fof(f28,plain,(
% 1.84/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.61    inference(nnf_transformation,[],[f2])).
% 1.84/0.61  fof(f2,axiom,(
% 1.84/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.61  fof(f65,plain,(
% 1.84/0.61    v1_relat_1(sK2) | ~spl4_3),
% 1.84/0.61    inference(avatar_component_clause,[],[f63])).
% 1.84/0.61  fof(f63,plain,(
% 1.84/0.61    spl4_3 <=> v1_relat_1(sK2)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.84/0.61  fof(f417,plain,(
% 1.84/0.61    ~spl4_11 | ~spl4_12 | spl4_4),
% 1.84/0.61    inference(avatar_split_clause,[],[f164,f69,f121,f117])).
% 1.84/0.61  fof(f121,plain,(
% 1.84/0.61    spl4_12 <=> r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.84/0.61  fof(f69,plain,(
% 1.84/0.61    spl4_4 <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.84/0.61  fof(f164,plain,(
% 1.84/0.61    ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) | spl4_4),
% 1.84/0.61    inference(trivial_inequality_removal,[],[f163])).
% 1.84/0.61  fof(f163,plain,(
% 1.84/0.61    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) | spl4_4),
% 1.84/0.61    inference(superposition,[],[f71,f42])).
% 1.84/0.61  fof(f42,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f21,plain,(
% 1.84/0.61    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f10])).
% 1.84/0.61  fof(f10,axiom,(
% 1.84/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.84/0.61  fof(f71,plain,(
% 1.84/0.61    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | spl4_4),
% 1.84/0.61    inference(avatar_component_clause,[],[f69])).
% 1.84/0.61  fof(f416,plain,(
% 1.84/0.61    ~spl4_2 | spl4_13),
% 1.84/0.61    inference(avatar_contradiction_clause,[],[f410])).
% 1.84/0.61  fof(f410,plain,(
% 1.84/0.61    $false | (~spl4_2 | spl4_13)),
% 1.84/0.61    inference(unit_resulting_resolution,[],[f195,f372,f86])).
% 1.84/0.61  fof(f86,plain,(
% 1.84/0.61    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK0,X0)) ) | ~spl4_2),
% 1.84/0.61    inference(resolution,[],[f44,f60])).
% 1.84/0.61  fof(f60,plain,(
% 1.84/0.61    r1_tarski(sK0,sK1) | ~spl4_2),
% 1.84/0.61    inference(avatar_component_clause,[],[f58])).
% 1.84/0.61  fof(f58,plain,(
% 1.84/0.61    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.84/0.61  fof(f44,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f24])).
% 1.84/0.61  fof(f24,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.84/0.61    inference(flattening,[],[f23])).
% 1.84/0.61  fof(f23,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.84/0.61    inference(ennf_transformation,[],[f4])).
% 1.84/0.61  fof(f4,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.84/0.61  fof(f372,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.84/0.61    inference(resolution,[],[f211,f46])).
% 1.84/0.61  fof(f46,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f5])).
% 1.84/0.61  fof(f5,axiom,(
% 1.84/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.84/0.61  fof(f211,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.84/0.61    inference(resolution,[],[f179,f48])).
% 1.84/0.61  % (9576)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.84/0.61  fof(f48,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f31])).
% 1.84/0.61  fof(f31,plain,(
% 1.84/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.84/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f30])).
% 1.84/0.61  fof(f30,plain,(
% 1.84/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.84/0.61    introduced(choice_axiom,[])).
% 1.84/0.61  fof(f25,plain,(
% 1.84/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.84/0.61    inference(ennf_transformation,[],[f15])).
% 1.84/0.61  fof(f15,plain,(
% 1.84/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.84/0.61    inference(rectify,[],[f1])).
% 1.84/0.61  fof(f1,axiom,(
% 1.84/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.84/0.61  fof(f179,plain,(
% 1.84/0.61    ( ! [X6,X4,X5] : (~r2_hidden(X6,k3_xboole_0(X5,X4)) | ~r1_xboole_0(X4,X5)) )),
% 1.84/0.61    inference(superposition,[],[f49,f91])).
% 1.84/0.61  fof(f91,plain,(
% 1.84/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.84/0.61    inference(superposition,[],[f73,f47])).
% 1.84/0.61  fof(f47,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f8])).
% 1.84/0.61  fof(f8,axiom,(
% 1.84/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.84/0.61  fof(f73,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.84/0.61    inference(superposition,[],[f47,f41])).
% 1.84/0.61  fof(f41,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f6])).
% 1.84/0.61  fof(f6,axiom,(
% 1.84/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.84/0.61  fof(f49,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f31])).
% 1.84/0.61  fof(f195,plain,(
% 1.84/0.61    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | spl4_13),
% 1.84/0.61    inference(avatar_component_clause,[],[f193])).
% 1.84/0.61  fof(f193,plain,(
% 1.84/0.61    spl4_13 <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.84/0.61  fof(f196,plain,(
% 1.84/0.61    ~spl4_13 | ~spl4_3 | spl4_12),
% 1.84/0.61    inference(avatar_split_clause,[],[f191,f121,f63,f193])).
% 1.84/0.61  fof(f191,plain,(
% 1.84/0.61    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | (~spl4_3 | spl4_12)),
% 1.84/0.61    inference(subsumption_resolution,[],[f186,f65])).
% 1.84/0.61  fof(f186,plain,(
% 1.84/0.61    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | ~v1_relat_1(sK2) | spl4_12),
% 1.84/0.61    inference(superposition,[],[f123,f150])).
% 1.84/0.61  fof(f150,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(subsumption_resolution,[],[f145,f50])).
% 1.84/0.61  fof(f145,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0))) )),
% 1.84/0.61    inference(duplicate_literal_removal,[],[f138])).
% 1.84/0.61  fof(f138,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(superposition,[],[f125,f132])).
% 1.84/0.61  fof(f125,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.84/0.61    inference(forward_demodulation,[],[f39,f40])).
% 1.84/0.61  fof(f39,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f20])).
% 1.84/0.61  fof(f20,plain,(
% 1.84/0.61    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f11])).
% 1.84/0.61  fof(f11,axiom,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 1.84/0.61  fof(f123,plain,(
% 1.84/0.61    ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | spl4_12),
% 1.84/0.61    inference(avatar_component_clause,[],[f121])).
% 1.84/0.61  fof(f72,plain,(
% 1.84/0.61    ~spl4_4 | spl4_1),
% 1.84/0.61    inference(avatar_split_clause,[],[f67,f53,f69])).
% 1.84/0.61  fof(f53,plain,(
% 1.84/0.61    spl4_1 <=> k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.84/0.61  fof(f67,plain,(
% 1.84/0.61    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | spl4_1),
% 1.84/0.61    inference(backward_demodulation,[],[f55,f40])).
% 1.84/0.61  fof(f55,plain,(
% 1.84/0.61    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) | spl4_1),
% 1.84/0.61    inference(avatar_component_clause,[],[f53])).
% 1.84/0.61  fof(f66,plain,(
% 1.84/0.61    spl4_3),
% 1.84/0.61    inference(avatar_split_clause,[],[f32,f63])).
% 1.84/0.61  fof(f32,plain,(
% 1.84/0.61    v1_relat_1(sK2)),
% 1.84/0.61    inference(cnf_transformation,[],[f27])).
% 1.84/0.61  fof(f27,plain,(
% 1.84/0.61    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.84/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).
% 1.84/0.61  fof(f26,plain,(
% 1.84/0.61    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.84/0.61    introduced(choice_axiom,[])).
% 1.84/0.61  fof(f17,plain,(
% 1.84/0.61    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.84/0.61    inference(flattening,[],[f16])).
% 1.84/0.61  fof(f16,plain,(
% 1.84/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.84/0.61    inference(ennf_transformation,[],[f14])).
% 1.84/0.61  fof(f14,negated_conjecture,(
% 1.84/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.84/0.61    inference(negated_conjecture,[],[f13])).
% 1.84/0.61  fof(f13,conjecture,(
% 1.84/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 1.84/0.61  fof(f61,plain,(
% 1.84/0.61    spl4_2),
% 1.84/0.61    inference(avatar_split_clause,[],[f33,f58])).
% 1.84/0.61  fof(f33,plain,(
% 1.84/0.61    r1_tarski(sK0,sK1)),
% 1.84/0.61    inference(cnf_transformation,[],[f27])).
% 1.84/0.61  fof(f56,plain,(
% 1.84/0.61    ~spl4_1),
% 1.84/0.61    inference(avatar_split_clause,[],[f34,f53])).
% 1.84/0.61  fof(f34,plain,(
% 1.84/0.61    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.84/0.61    inference(cnf_transformation,[],[f27])).
% 1.84/0.61  % SZS output end Proof for theBenchmark
% 1.84/0.61  % (9580)------------------------------
% 1.84/0.61  % (9580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (9580)Termination reason: Refutation
% 1.84/0.61  
% 1.84/0.61  % (9580)Memory used [KB]: 6524
% 1.84/0.61  % (9580)Time elapsed: 0.178 s
% 1.84/0.61  % (9580)------------------------------
% 1.84/0.61  % (9580)------------------------------
% 1.84/0.62  % (9558)Success in time 0.249 s
%------------------------------------------------------------------------------
