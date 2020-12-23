%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:28 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 140 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 ( 413 expanded)
%              Number of equality atoms :   39 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f150,f162,f168,f653])).

fof(f653,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f628,f161])).

fof(f161,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_8
  <=> r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f628,plain,(
    ! [X0,X1] : r1_xboole_0(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f618,f53])).

fof(f53,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    & v2_funct_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
        & v2_funct_1(X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))
      & v2_funct_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f618,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
      | r1_xboole_0(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f186,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(backward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f37,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f186,plain,(
    ! [X10,X11] :
      ( k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X10,X11))
      | r1_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11)) ) ),
    inference(superposition,[],[f42,f147])).

fof(f147,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f146,f29])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f145,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f166,f29])).

fof(f166,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f165,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f164,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f157,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f157,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_7
  <=> r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f162,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_2 ),
    inference(avatar_split_clause,[],[f153,f79,f159,f155])).

fof(f79,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f153,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl3_2 ),
    inference(resolution,[],[f81,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_subset_1(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f81,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f150,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f148,f29])).

fof(f148,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f77,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

fof(f77,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f73,f75,f79])).

fof(f73,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(extensionality_resolution,[],[f40,f32])).

fof(f32,plain,(
    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (30343)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (30325)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (30334)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (30335)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (30327)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (30323)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (30341)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (30342)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (30322)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (30333)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (30324)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (30350)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (30350)Refutation not found, incomplete strategy% (30350)------------------------------
% 0.22/0.53  % (30350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30350)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30350)Memory used [KB]: 1663
% 0.22/0.53  % (30350)Time elapsed: 0.112 s
% 0.22/0.53  % (30350)------------------------------
% 0.22/0.53  % (30350)------------------------------
% 0.22/0.53  % (30339)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (30337)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (30326)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (30337)Refutation not found, incomplete strategy% (30337)------------------------------
% 0.22/0.53  % (30337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30337)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30337)Memory used [KB]: 10618
% 0.22/0.53  % (30337)Time elapsed: 0.128 s
% 0.22/0.53  % (30337)------------------------------
% 0.22/0.53  % (30337)------------------------------
% 0.22/0.53  % (30331)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (30336)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (30321)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (30340)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (30349)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (30345)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (30349)Refutation not found, incomplete strategy% (30349)------------------------------
% 0.22/0.54  % (30349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30349)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30349)Memory used [KB]: 10618
% 0.22/0.54  % (30349)Time elapsed: 0.132 s
% 0.22/0.54  % (30349)------------------------------
% 0.22/0.54  % (30349)------------------------------
% 0.22/0.54  % (30344)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (30330)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (30338)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.55  % (30329)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.55  % (30332)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (30346)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.55  % (30331)Refutation not found, incomplete strategy% (30331)------------------------------
% 1.44/0.55  % (30331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (30331)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (30331)Memory used [KB]: 10618
% 1.44/0.55  % (30331)Time elapsed: 0.143 s
% 1.44/0.55  % (30331)------------------------------
% 1.44/0.55  % (30331)------------------------------
% 1.44/0.55  % (30328)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.56  % (30327)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f656,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f83,f150,f162,f168,f653])).
% 1.44/0.56  fof(f653,plain,(
% 1.44/0.56    spl3_8),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f642])).
% 1.44/0.56  fof(f642,plain,(
% 1.44/0.56    $false | spl3_8),
% 1.44/0.56    inference(resolution,[],[f628,f161])).
% 1.44/0.56  fof(f161,plain,(
% 1.44/0.56    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) | spl3_8),
% 1.44/0.56    inference(avatar_component_clause,[],[f159])).
% 1.44/0.56  fof(f159,plain,(
% 1.44/0.56    spl3_8 <=> r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.44/0.56  fof(f628,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X1))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f618,f53])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.44/0.56    inference(resolution,[],[f33,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    v1_relat_1(sK2)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) & v2_funct_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ? [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) & v2_funct_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ? [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.44/0.56    inference(flattening,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ? [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.44/0.56    inference(ennf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.44/0.56    inference(negated_conjecture,[],[f12])).
% 1.44/0.56  fof(f12,conjecture,(
% 1.44/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 1.44/0.56  fof(f618,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) | r1_xboole_0(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X1))) )),
% 1.44/0.56    inference(superposition,[],[f186,f61])).
% 1.44/0.56  fof(f61,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 1.44/0.56    inference(resolution,[],[f59,f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(nnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 1.44/0.56    inference(backward_demodulation,[],[f48,f49])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f37,f35,f35])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f36,f35])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.44/0.56  fof(f186,plain,(
% 1.44/0.56    ( ! [X10,X11] : (k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X10,X11)) | r1_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11))) )),
% 1.44/0.56    inference(superposition,[],[f42,f147])).
% 1.44/0.56  fof(f147,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f146,f29])).
% 1.44/0.56  fof(f146,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f145,f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    v1_funct_1(sK2)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f145,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.44/0.56    inference(resolution,[],[f45,f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    v2_funct_1(sK2)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(flattening,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f168,plain,(
% 1.44/0.56    spl3_7),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f167])).
% 1.44/0.56  fof(f167,plain,(
% 1.44/0.56    $false | spl3_7),
% 1.44/0.56    inference(subsumption_resolution,[],[f166,f29])).
% 1.44/0.56  fof(f166,plain,(
% 1.44/0.56    ~v1_relat_1(sK2) | spl3_7),
% 1.44/0.56    inference(subsumption_resolution,[],[f165,f51])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.56    inference(equality_resolution,[],[f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.56    inference(flattening,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.56  fof(f165,plain,(
% 1.44/0.56    ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | spl3_7),
% 1.44/0.56    inference(subsumption_resolution,[],[f164,f47])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f34,f35])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.44/0.56  fof(f164,plain,(
% 1.44/0.56    ~r1_tarski(k6_subset_1(sK0,sK1),sK0) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | spl3_7),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f163])).
% 1.44/0.56  fof(f163,plain,(
% 1.44/0.56    ~r1_tarski(k6_subset_1(sK0,sK1),sK0) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | spl3_7),
% 1.44/0.56    inference(resolution,[],[f157,f44])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(flattening,[],[f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 1.44/0.56  fof(f157,plain,(
% 1.44/0.56    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) | spl3_7),
% 1.44/0.56    inference(avatar_component_clause,[],[f155])).
% 1.44/0.56  fof(f155,plain,(
% 1.44/0.56    spl3_7 <=> r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.44/0.56  fof(f162,plain,(
% 1.44/0.56    ~spl3_7 | ~spl3_8 | spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f153,f79,f159,f155])).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.56  fof(f153,plain,(
% 1.44/0.56    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) | spl3_2),
% 1.44/0.56    inference(resolution,[],[f81,f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_subset_1(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f46,f35])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.44/0.56    inference(flattening,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.44/0.56  fof(f81,plain,(
% 1.44/0.56    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | spl3_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f79])).
% 1.44/0.56  fof(f150,plain,(
% 1.44/0.56    spl3_1),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f149])).
% 1.44/0.56  fof(f149,plain,(
% 1.44/0.56    $false | spl3_1),
% 1.44/0.56    inference(subsumption_resolution,[],[f148,f29])).
% 1.44/0.56  fof(f148,plain,(
% 1.44/0.56    ~v1_relat_1(sK2) | spl3_1),
% 1.44/0.56    inference(resolution,[],[f77,f43])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(ennf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).
% 1.44/0.56  fof(f77,plain,(
% 1.44/0.56    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl3_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f75])).
% 1.44/0.56  fof(f75,plain,(
% 1.44/0.56    spl3_1 <=> r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.56  fof(f83,plain,(
% 1.44/0.56    ~spl3_2 | ~spl3_1),
% 1.44/0.56    inference(avatar_split_clause,[],[f73,f75,f79])).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.44/0.56    inference(extensionality_resolution,[],[f40,f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (30327)------------------------------
% 1.44/0.56  % (30327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (30327)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (30327)Memory used [KB]: 11129
% 1.44/0.56  % (30327)Time elapsed: 0.089 s
% 1.44/0.56  % (30327)------------------------------
% 1.44/0.56  % (30327)------------------------------
% 1.44/0.56  % (30320)Success in time 0.193 s
%------------------------------------------------------------------------------
