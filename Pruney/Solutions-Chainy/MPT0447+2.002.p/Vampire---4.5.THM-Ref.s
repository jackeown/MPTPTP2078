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
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 6.43s
% Output     : Refutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 644 expanded)
%              Number of leaves         :   42 ( 207 expanded)
%              Depth                    :   22
%              Number of atoms          :  489 (1720 expanded)
%              Number of equality atoms :   52 ( 306 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6966,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f85,f5061,f88,f6950,f339])).

fof(f339,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | r1_tarski(k3_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f149,f139])).

fof(f139,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f94,f137])).

fof(f137,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f109,f135])).

fof(f135,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f108,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f108,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f109,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f94,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f134,f137])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f6950,plain,(
    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f6917,f86])).

fof(f86,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(X1))
          & r1_tarski(sK1,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(X1))
        & r1_tarski(sK1,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f6917,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f5253,f341])).

fof(f341,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k6_subset_1(X5,k1_relat_1(X4)),k2_relat_1(X4))
      | r1_tarski(X5,k3_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f148,f139])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f132,f137,f106])).

fof(f106,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f5253,plain,(
    ! [X15] : r1_tarski(k6_subset_1(k2_relat_1(sK1),X15),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f5220,f138])).

fof(f138,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f92,f106])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f5220,plain,(
    ! [X15] : r1_tarski(k6_subset_1(k6_subset_1(k2_relat_1(sK1),k1_xboole_0),X15),k2_relat_1(sK2)) ),
    inference(superposition,[],[f691,f3834])).

fof(f3834,plain,(
    k1_xboole_0 = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f3833,f842])).

fof(f842,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f713,f177])).

fof(f177,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f117,f91])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f713,plain,(
    ! [X9] : r1_tarski(k2_relat_1(k1_xboole_0),X9) ),
    inference(resolution,[],[f640,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f640,plain,(
    ! [X9] : ~ r2_hidden(X9,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f632,f157])).

fof(f157,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f93,f89])).

fof(f89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f632,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f600,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f68])).

fof(f68,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK6(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f600,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f423,f152])).

fof(f152,plain,(
    ! [X0] : sP0(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f27,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ sP0(k1_xboole_0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f418,f121])).

fof(f121,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f77,f80,f79,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f418,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(resolution,[],[f226,f97])).

fof(f97,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(X4,sK4(X0,X2))
                | ~ r1_tarski(X4,X2) )
            & r2_hidden(sK4(X0,X2),sK3(X0)) )
          | ~ r2_hidden(X2,sK3(X0)) )
      & ! [X5,X6] :
          ( r2_hidden(X6,sK3(X0))
          | ~ r1_tarski(X6,X5)
          | ~ r2_hidden(X5,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f62,f64,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X4,X3)
                      | ~ r1_tarski(X4,X2) )
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & ! [X5,X6] :
              ( r2_hidden(X6,X1)
              | ~ r1_tarski(X6,X5)
              | ~ r2_hidden(X5,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( r2_hidden(X4,X3)
                    | ~ r1_tarski(X4,X2) )
                & r2_hidden(X3,sK3(X0)) )
            | ~ r2_hidden(X2,sK3(X0)) )
        & ! [X6,X5] :
            ( r2_hidden(X6,sK3(X0))
            | ~ r1_tarski(X6,X5)
            | ~ r2_hidden(X5,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(X4,X3)
              | ~ r1_tarski(X4,X2) )
          & r2_hidden(X3,sK3(X0)) )
     => ( ! [X4] :
            ( r2_hidden(X4,sK4(X0,X2))
            | ~ r1_tarski(X4,X2) )
        & r2_hidden(sK4(X0,X2),sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X3)
                  | ~ r1_tarski(X4,X2) )
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X1) )
      & ! [X5,X6] :
          ( r2_hidden(X6,X1)
          | ~ r1_tarski(X6,X5)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f34])).

fof(f34,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

fof(f226,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK11(k1_xboole_0),X6)
      | ~ r2_hidden(X7,k1_xboole_0) ) ),
    inference(resolution,[],[f171,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK11(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK11(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f50,f83])).

fof(f83,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK11(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK11(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f113,f90])).

fof(f90,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f3833,plain,(
    k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f3832,f91])).

fof(f3832,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)))
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f3831,f842])).

fof(f3831,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)))
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f3830,f86])).

fof(f3830,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)))
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f3801,f85])).

fof(f3801,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f278,f3760])).

fof(f3760,plain,(
    k1_xboole_0 = k6_subset_1(sK1,sK2) ),
    inference(resolution,[],[f3717,f177])).

fof(f3717,plain,(
    ! [X70] : r1_tarski(k6_subset_1(sK1,sK2),X70) ),
    inference(resolution,[],[f819,f207])).

fof(f207,plain,(
    ! [X1] : r1_tarski(k6_subset_1(sK1,X1),sK2) ),
    inference(resolution,[],[f191,f142])).

fof(f142,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f103,f106])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f191,plain,(
    ! [X13] :
      ( ~ r1_tarski(X13,sK1)
      | r1_tarski(X13,sK2) ) ),
    inference(resolution,[],[f133,f87])).

fof(f87,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f819,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(k6_subset_1(X5,X7),X6)
      | r1_tarski(k6_subset_1(X5,X6),X7) ) ),
    inference(resolution,[],[f262,f148])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | r1_tarski(k6_subset_1(X2,X0),X1) ) ),
    inference(superposition,[],[f147,f144])).

fof(f144,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f105,f135,f135])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f131,f106,f137])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f278,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(k6_subset_1(X4,X3)),k6_subset_1(k2_relat_1(X4),k2_relat_1(X3)))
      | ~ v1_relat_1(X4)
      | k2_relat_1(k6_subset_1(X4,X3)) = k6_subset_1(k2_relat_1(X4),k2_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f95,f117])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f691,plain,(
    ! [X19,X17,X18] : r1_tarski(k6_subset_1(k6_subset_1(X18,k6_subset_1(X18,X17)),X19),X17) ),
    inference(forward_demodulation,[],[f677,f145])).

fof(f145,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f110,f136,f106,f106])).

fof(f136,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f107,f135])).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f110,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f677,plain,(
    ! [X19,X17,X18] : r1_tarski(k6_subset_1(k1_setfam_1(k2_enumset1(X18,X18,X18,X17)),X19),X17) ),
    inference(superposition,[],[f299,f237])).

fof(f237,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(superposition,[],[f145,f144])).

fof(f299,plain,(
    ! [X10,X11,X9] : r1_tarski(k6_subset_1(k6_subset_1(X9,X10),X11),X9) ),
    inference(superposition,[],[f142,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f130,f106,f106,f106,f137])).

fof(f130,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f88,plain,(
    ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f5061,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f5047,f86])).

fof(f5047,plain,
    ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f4975,f386])).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X0))
      | r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f343,f133])).

fof(f343,plain,(
    ! [X8] :
      ( r1_tarski(k1_relat_1(X8),k3_relat_1(X8))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f141,f139])).

fof(f141,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f102,f137])).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f4975,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f4953,f138])).

fof(f4953,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_xboole_0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f3829,f819])).

fof(f3829,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3828,f700])).

fof(f700,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f633,f177])).

fof(f633,plain,(
    ! [X10] : r1_tarski(k1_relat_1(k1_xboole_0),X10) ),
    inference(resolution,[],[f600,f119])).

fof(f3828,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f3827,f85])).

fof(f3827,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f3793,f86])).

fof(f3793,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f96,f3760])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f85,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (5796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (5811)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (5803)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (5804)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (5789)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (5795)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (5794)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (5799)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (5798)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (5812)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (5793)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5801)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5809)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (5790)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5791)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (5816)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (5792)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (5817)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (5818)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5815)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (5810)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (5808)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (5814)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (5807)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.55  % (5800)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.55  % (5802)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.55  % (5806)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.55  % (5805)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (5797)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.56  % (5813)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 3.26/0.81  % (5794)Time limit reached!
% 3.26/0.81  % (5794)------------------------------
% 3.26/0.81  % (5794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (5794)Termination reason: Time limit
% 3.26/0.81  
% 3.26/0.81  % (5794)Memory used [KB]: 8827
% 3.26/0.81  % (5794)Time elapsed: 0.407 s
% 3.26/0.81  % (5794)------------------------------
% 3.26/0.81  % (5794)------------------------------
% 4.01/0.90  % (5789)Time limit reached!
% 4.01/0.90  % (5789)------------------------------
% 4.01/0.90  % (5789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.90  % (5789)Termination reason: Time limit
% 4.01/0.90  
% 4.01/0.90  % (5789)Memory used [KB]: 3326
% 4.01/0.90  % (5789)Time elapsed: 0.502 s
% 4.01/0.90  % (5789)------------------------------
% 4.01/0.90  % (5789)------------------------------
% 4.01/0.91  % (5806)Time limit reached!
% 4.01/0.91  % (5806)------------------------------
% 4.01/0.91  % (5806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (5806)Termination reason: Time limit
% 4.01/0.91  
% 4.01/0.91  % (5806)Memory used [KB]: 12920
% 4.01/0.91  % (5806)Time elapsed: 0.509 s
% 4.01/0.91  % (5806)------------------------------
% 4.01/0.91  % (5806)------------------------------
% 4.01/0.91  % (5801)Time limit reached!
% 4.01/0.91  % (5801)------------------------------
% 4.01/0.91  % (5801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (5801)Termination reason: Time limit
% 4.01/0.91  % (5801)Termination phase: Saturation
% 4.01/0.91  
% 4.01/0.91  % (5801)Memory used [KB]: 9210
% 4.01/0.91  % (5801)Time elapsed: 0.500 s
% 4.01/0.91  % (5801)------------------------------
% 4.01/0.91  % (5801)------------------------------
% 4.01/0.92  % (5790)Time limit reached!
% 4.01/0.92  % (5790)------------------------------
% 4.01/0.92  % (5790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (5790)Termination reason: Time limit
% 4.01/0.92  % (5790)Termination phase: Saturation
% 4.01/0.92  
% 4.01/0.92  % (5790)Memory used [KB]: 8443
% 4.01/0.92  % (5790)Time elapsed: 0.500 s
% 4.01/0.92  % (5790)------------------------------
% 4.01/0.92  % (5790)------------------------------
% 4.67/0.98  % (5820)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.67/1.00  % (5817)Time limit reached!
% 4.67/1.00  % (5817)------------------------------
% 4.67/1.00  % (5817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.67/1.00  % (5817)Termination reason: Time limit
% 4.67/1.00  % (5817)Termination phase: Saturation
% 4.67/1.00  
% 4.67/1.00  % (5817)Memory used [KB]: 8315
% 4.67/1.00  % (5817)Time elapsed: 0.602 s
% 4.67/1.00  % (5817)------------------------------
% 4.67/1.00  % (5817)------------------------------
% 4.67/1.00  % (5799)Time limit reached!
% 4.67/1.00  % (5799)------------------------------
% 4.67/1.00  % (5799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.67/1.00  % (5799)Termination reason: Time limit
% 4.67/1.00  % (5799)Termination phase: Saturation
% 4.67/1.00  
% 4.67/1.00  % (5799)Memory used [KB]: 17014
% 4.67/1.00  % (5799)Time elapsed: 0.500 s
% 4.67/1.00  % (5799)------------------------------
% 4.67/1.00  % (5799)------------------------------
% 4.67/1.01  % (5796)Time limit reached!
% 4.67/1.01  % (5796)------------------------------
% 4.67/1.01  % (5796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.67/1.01  % (5796)Termination reason: Time limit
% 4.67/1.01  % (5796)Termination phase: Saturation
% 4.67/1.01  
% 4.67/1.01  % (5796)Memory used [KB]: 12153
% 4.67/1.01  % (5796)Time elapsed: 0.600 s
% 4.67/1.01  % (5796)------------------------------
% 4.67/1.01  % (5796)------------------------------
% 4.67/1.01  % (5821)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.67/1.02  % (5805)Time limit reached!
% 4.67/1.02  % (5805)------------------------------
% 4.67/1.02  % (5805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.18/1.03  % (5805)Termination reason: Time limit
% 5.18/1.03  % (5805)Termination phase: Saturation
% 5.18/1.03  
% 5.18/1.03  % (5805)Memory used [KB]: 17398
% 5.18/1.03  % (5805)Time elapsed: 0.600 s
% 5.18/1.03  % (5805)------------------------------
% 5.18/1.03  % (5805)------------------------------
% 5.18/1.03  % (5822)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.18/1.04  % (5823)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.18/1.07  % (5824)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.68/1.13  % (5825)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.68/1.15  % (5826)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.22/1.16  % (5827)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.22/1.17  % (5828)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.43/1.20  % (5818)Refutation found. Thanks to Tanya!
% 6.43/1.20  % SZS status Theorem for theBenchmark
% 6.43/1.20  % SZS output start Proof for theBenchmark
% 6.43/1.20  fof(f6966,plain,(
% 6.43/1.20    $false),
% 6.43/1.20    inference(unit_resulting_resolution,[],[f85,f5061,f88,f6950,f339])).
% 6.43/1.20  fof(f339,plain,(
% 6.43/1.20    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | r1_tarski(k3_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 6.43/1.20    inference(superposition,[],[f149,f139])).
% 6.43/1.20  fof(f139,plain,(
% 6.43/1.20    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 6.43/1.20    inference(definition_unfolding,[],[f94,f137])).
% 6.43/1.20  fof(f137,plain,(
% 6.43/1.20    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 6.43/1.20    inference(definition_unfolding,[],[f109,f135])).
% 6.43/1.20  fof(f135,plain,(
% 6.43/1.20    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 6.43/1.20    inference(definition_unfolding,[],[f108,f129])).
% 6.43/1.20  fof(f129,plain,(
% 6.43/1.20    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f20])).
% 6.43/1.20  fof(f20,axiom,(
% 6.43/1.20    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 6.43/1.20  fof(f108,plain,(
% 6.43/1.20    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f19])).
% 6.43/1.20  fof(f19,axiom,(
% 6.43/1.20    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.43/1.20  fof(f109,plain,(
% 6.43/1.20    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.43/1.20    inference(cnf_transformation,[],[f21])).
% 6.43/1.20  fof(f21,axiom,(
% 6.43/1.20    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.43/1.20  fof(f94,plain,(
% 6.43/1.20    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f41])).
% 6.43/1.20  fof(f41,plain,(
% 6.43/1.20    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 6.43/1.20    inference(ennf_transformation,[],[f28])).
% 6.43/1.20  fof(f28,axiom,(
% 6.43/1.20    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 6.43/1.20  fof(f149,plain,(
% 6.43/1.20    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 6.43/1.20    inference(definition_unfolding,[],[f134,f137])).
% 6.43/1.20  fof(f134,plain,(
% 6.43/1.20    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f56])).
% 6.43/1.20  fof(f56,plain,(
% 6.43/1.20    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 6.43/1.20    inference(flattening,[],[f55])).
% 6.43/1.20  fof(f55,plain,(
% 6.43/1.20    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 6.43/1.20    inference(ennf_transformation,[],[f17])).
% 6.43/1.20  fof(f17,axiom,(
% 6.43/1.20    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 6.43/1.20  fof(f6950,plain,(
% 6.43/1.20    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2))),
% 6.43/1.20    inference(subsumption_resolution,[],[f6917,f86])).
% 6.43/1.20  fof(f86,plain,(
% 6.43/1.20    v1_relat_1(sK2)),
% 6.43/1.20    inference(cnf_transformation,[],[f61])).
% 6.43/1.20  fof(f61,plain,(
% 6.43/1.20    (~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 6.43/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f60,f59])).
% 6.43/1.20  fof(f59,plain,(
% 6.43/1.20    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK1),k3_relat_1(X1)) & r1_tarski(sK1,X1) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f60,plain,(
% 6.43/1.20    ? [X1] : (~r1_tarski(k3_relat_1(sK1),k3_relat_1(X1)) & r1_tarski(sK1,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f39,plain,(
% 6.43/1.20    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 6.43/1.20    inference(flattening,[],[f38])).
% 6.43/1.20  fof(f38,plain,(
% 6.43/1.20    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 6.43/1.20    inference(ennf_transformation,[],[f33])).
% 6.43/1.20  fof(f33,negated_conjecture,(
% 6.43/1.20    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 6.43/1.20    inference(negated_conjecture,[],[f32])).
% 6.43/1.20  fof(f32,conjecture,(
% 6.43/1.20    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 6.43/1.20  fof(f6917,plain,(
% 6.43/1.20    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 6.43/1.20    inference(resolution,[],[f5253,f341])).
% 6.43/1.20  fof(f341,plain,(
% 6.43/1.20    ( ! [X4,X5] : (~r1_tarski(k6_subset_1(X5,k1_relat_1(X4)),k2_relat_1(X4)) | r1_tarski(X5,k3_relat_1(X4)) | ~v1_relat_1(X4)) )),
% 6.43/1.20    inference(superposition,[],[f148,f139])).
% 6.43/1.20  fof(f148,plain,(
% 6.43/1.20    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 6.43/1.20    inference(definition_unfolding,[],[f132,f137,f106])).
% 6.43/1.20  fof(f106,plain,(
% 6.43/1.20    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f24])).
% 6.43/1.20  fof(f24,axiom,(
% 6.43/1.20    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 6.43/1.20  fof(f132,plain,(
% 6.43/1.20    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f52])).
% 6.43/1.20  fof(f52,plain,(
% 6.43/1.20    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.43/1.20    inference(ennf_transformation,[],[f13])).
% 6.43/1.20  fof(f13,axiom,(
% 6.43/1.20    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 6.43/1.20  fof(f5253,plain,(
% 6.43/1.20    ( ! [X15] : (r1_tarski(k6_subset_1(k2_relat_1(sK1),X15),k2_relat_1(sK2))) )),
% 6.43/1.20    inference(forward_demodulation,[],[f5220,f138])).
% 6.43/1.20  fof(f138,plain,(
% 6.43/1.20    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 6.43/1.20    inference(definition_unfolding,[],[f92,f106])).
% 6.43/1.20  fof(f92,plain,(
% 6.43/1.20    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.43/1.20    inference(cnf_transformation,[],[f10])).
% 6.43/1.20  fof(f10,axiom,(
% 6.43/1.20    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 6.43/1.20  fof(f5220,plain,(
% 6.43/1.20    ( ! [X15] : (r1_tarski(k6_subset_1(k6_subset_1(k2_relat_1(sK1),k1_xboole_0),X15),k2_relat_1(sK2))) )),
% 6.43/1.20    inference(superposition,[],[f691,f3834])).
% 6.43/1.20  fof(f3834,plain,(
% 6.43/1.20    k1_xboole_0 = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))),
% 6.43/1.20    inference(forward_demodulation,[],[f3833,f842])).
% 6.43/1.20  fof(f842,plain,(
% 6.43/1.20    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 6.43/1.20    inference(resolution,[],[f713,f177])).
% 6.43/1.20  fof(f177,plain,(
% 6.43/1.20    ( ! [X5] : (~r1_tarski(X5,k1_xboole_0) | k1_xboole_0 = X5) )),
% 6.43/1.20    inference(resolution,[],[f117,f91])).
% 6.43/1.20  fof(f91,plain,(
% 6.43/1.20    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f8])).
% 6.43/1.20  fof(f8,axiom,(
% 6.43/1.20    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.43/1.20  fof(f117,plain,(
% 6.43/1.20    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f71])).
% 6.43/1.20  fof(f71,plain,(
% 6.43/1.20    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.43/1.20    inference(flattening,[],[f70])).
% 6.43/1.20  fof(f70,plain,(
% 6.43/1.20    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.43/1.20    inference(nnf_transformation,[],[f6])).
% 6.43/1.20  fof(f6,axiom,(
% 6.43/1.20    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.43/1.20  fof(f713,plain,(
% 6.43/1.20    ( ! [X9] : (r1_tarski(k2_relat_1(k1_xboole_0),X9)) )),
% 6.43/1.20    inference(resolution,[],[f640,f119])).
% 6.43/1.20  fof(f119,plain,(
% 6.43/1.20    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f75])).
% 6.43/1.20  fof(f75,plain,(
% 6.43/1.20    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.43/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).
% 6.43/1.20  fof(f74,plain,(
% 6.43/1.20    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f73,plain,(
% 6.43/1.20    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.43/1.20    inference(rectify,[],[f72])).
% 6.43/1.20  fof(f72,plain,(
% 6.43/1.20    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.43/1.20    inference(nnf_transformation,[],[f49])).
% 6.43/1.20  fof(f49,plain,(
% 6.43/1.20    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.43/1.20    inference(ennf_transformation,[],[f2])).
% 6.43/1.20  fof(f2,axiom,(
% 6.43/1.20    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.43/1.20  fof(f640,plain,(
% 6.43/1.20    ( ! [X9] : (~r2_hidden(X9,k2_relat_1(k1_xboole_0))) )),
% 6.43/1.20    inference(subsumption_resolution,[],[f632,f157])).
% 6.43/1.20  fof(f157,plain,(
% 6.43/1.20    v1_relat_1(k1_xboole_0)),
% 6.43/1.20    inference(resolution,[],[f93,f89])).
% 6.43/1.20  fof(f89,plain,(
% 6.43/1.20    v1_xboole_0(k1_xboole_0)),
% 6.43/1.20    inference(cnf_transformation,[],[f3])).
% 6.43/1.20  fof(f3,axiom,(
% 6.43/1.20    v1_xboole_0(k1_xboole_0)),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 6.43/1.20  fof(f93,plain,(
% 6.43/1.20    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f40])).
% 6.43/1.20  fof(f40,plain,(
% 6.43/1.20    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 6.43/1.20    inference(ennf_transformation,[],[f26])).
% 6.43/1.20  fof(f26,axiom,(
% 6.43/1.20    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 6.43/1.20  fof(f632,plain,(
% 6.43/1.20    ( ! [X9] : (~r2_hidden(X9,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 6.43/1.20    inference(resolution,[],[f600,f114])).
% 6.43/1.20  fof(f114,plain,(
% 6.43/1.20    ( ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f69])).
% 6.43/1.20  fof(f69,plain,(
% 6.43/1.20    ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.43/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f68])).
% 6.43/1.20  fof(f68,plain,(
% 6.43/1.20    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK6(X1),k1_relat_1(X1)))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f48,plain,(
% 6.43/1.20    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.43/1.20    inference(flattening,[],[f47])).
% 6.43/1.20  fof(f47,plain,(
% 6.43/1.20    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.43/1.20    inference(ennf_transformation,[],[f30])).
% 6.43/1.20  fof(f30,axiom,(
% 6.43/1.20    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 6.43/1.20  fof(f600,plain,(
% 6.43/1.20    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 6.43/1.20    inference(resolution,[],[f423,f152])).
% 6.43/1.20  fof(f152,plain,(
% 6.43/1.20    ( ! [X0] : (sP0(X0,k1_relat_1(X0))) )),
% 6.43/1.20    inference(equality_resolution,[],[f125])).
% 6.43/1.20  fof(f125,plain,(
% 6.43/1.20    ( ! [X0,X1] : (sP0(X0,X1) | k1_relat_1(X0) != X1) )),
% 6.43/1.20    inference(cnf_transformation,[],[f82])).
% 6.43/1.20  fof(f82,plain,(
% 6.43/1.20    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 6.43/1.20    inference(nnf_transformation,[],[f58])).
% 6.43/1.20  fof(f58,plain,(
% 6.43/1.20    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 6.43/1.20    inference(definition_folding,[],[f27,f57])).
% 6.43/1.20  fof(f57,plain,(
% 6.43/1.20    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.43/1.20    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.43/1.20  fof(f27,axiom,(
% 6.43/1.20    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.43/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 6.43/1.20  fof(f423,plain,(
% 6.43/1.20    ( ! [X0,X1] : (~sP0(k1_xboole_0,X1) | ~r2_hidden(X0,X1)) )),
% 6.43/1.20    inference(resolution,[],[f418,f121])).
% 6.43/1.20  fof(f121,plain,(
% 6.43/1.20    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 6.43/1.20    inference(cnf_transformation,[],[f81])).
% 6.43/1.20  fof(f81,plain,(
% 6.43/1.20    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 6.43/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f77,f80,f79,f78])).
% 6.43/1.20  fof(f78,plain,(
% 6.43/1.20    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f79,plain,(
% 6.43/1.20    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f80,plain,(
% 6.43/1.20    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f77,plain,(
% 6.43/1.20    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 6.43/1.20    inference(rectify,[],[f76])).
% 6.43/1.20  fof(f76,plain,(
% 6.43/1.20    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 6.43/1.20    inference(nnf_transformation,[],[f57])).
% 6.43/1.20  fof(f418,plain,(
% 6.43/1.20    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 6.43/1.20    inference(resolution,[],[f226,f97])).
% 6.43/1.20  fof(f97,plain,(
% 6.43/1.20    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 6.43/1.20    inference(cnf_transformation,[],[f65])).
% 6.43/1.20  fof(f65,plain,(
% 6.43/1.20    ! [X0] : (! [X2] : ((! [X4] : (r2_hidden(X4,sK4(X0,X2)) | ~r1_tarski(X4,X2)) & r2_hidden(sK4(X0,X2),sK3(X0))) | ~r2_hidden(X2,sK3(X0))) & ! [X5,X6] : (r2_hidden(X6,sK3(X0)) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 6.43/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f62,f64,f63])).
% 6.43/1.20  fof(f63,plain,(
% 6.43/1.20    ! [X0] : (? [X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X1)) & ! [X5,X6] : (r2_hidden(X6,X1) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,X1)) & r2_hidden(X0,X1)) => (! [X2] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,sK3(X0))) | ~r2_hidden(X2,sK3(X0))) & ! [X6,X5] : (r2_hidden(X6,sK3(X0)) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f64,plain,(
% 6.43/1.20    ! [X2,X0] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,sK3(X0))) => (! [X4] : (r2_hidden(X4,sK4(X0,X2)) | ~r1_tarski(X4,X2)) & r2_hidden(sK4(X0,X2),sK3(X0))))),
% 6.43/1.20    introduced(choice_axiom,[])).
% 6.43/1.20  fof(f62,plain,(
% 6.43/1.20    ! [X0] : ? [X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X1)) & ! [X5,X6] : (r2_hidden(X6,X1) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 6.43/1.20    inference(rectify,[],[f45])).
% 6.43/1.21  fof(f45,plain,(
% 6.43/1.21    ! [X0] : ? [X1] : (! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 6.43/1.21    inference(flattening,[],[f44])).
% 6.43/1.21  fof(f44,plain,(
% 6.43/1.21    ! [X0] : ? [X1] : (! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 6.43/1.21    inference(ennf_transformation,[],[f37])).
% 6.43/1.21  fof(f37,plain,(
% 6.43/1.21    ! [X0] : ? [X1] : (! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 6.43/1.21    inference(pure_predicate_removal,[],[f34])).
% 6.43/1.21  fof(f34,plain,(
% 6.43/1.21    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 6.43/1.21    inference(rectify,[],[f23])).
% 6.43/1.21  fof(f23,axiom,(
% 6.43/1.21    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).
% 6.43/1.21  fof(f226,plain,(
% 6.43/1.21    ( ! [X6,X7] : (~r2_hidden(sK11(k1_xboole_0),X6) | ~r2_hidden(X7,k1_xboole_0)) )),
% 6.43/1.21    inference(resolution,[],[f171,f127])).
% 6.43/1.21  fof(f127,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r2_hidden(sK11(X1),X1) | ~r2_hidden(X0,X1)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f84])).
% 6.43/1.21  fof(f84,plain,(
% 6.43/1.21    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK11(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK11(X1),X1)) | ~r2_hidden(X0,X1))),
% 6.43/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f50,f83])).
% 6.43/1.21  fof(f83,plain,(
% 6.43/1.21    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK11(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK11(X1),X1)))),
% 6.43/1.21    introduced(choice_axiom,[])).
% 6.43/1.21  fof(f50,plain,(
% 6.43/1.21    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 6.43/1.21    inference(ennf_transformation,[],[f22])).
% 6.43/1.21  fof(f22,axiom,(
% 6.43/1.21    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 6.43/1.21  fof(f171,plain,(
% 6.43/1.21    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 6.43/1.21    inference(resolution,[],[f113,f90])).
% 6.43/1.21  fof(f90,plain,(
% 6.43/1.21    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f15])).
% 6.43/1.21  fof(f15,axiom,(
% 6.43/1.21    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 6.43/1.21  fof(f113,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f67])).
% 6.43/1.21  fof(f67,plain,(
% 6.43/1.21    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 6.43/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f66])).
% 6.43/1.21  fof(f66,plain,(
% 6.43/1.21    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 6.43/1.21    introduced(choice_axiom,[])).
% 6.43/1.21  fof(f46,plain,(
% 6.43/1.21    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 6.43/1.21    inference(ennf_transformation,[],[f36])).
% 6.43/1.21  fof(f36,plain,(
% 6.43/1.21    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.43/1.21    inference(rectify,[],[f5])).
% 6.43/1.21  fof(f5,axiom,(
% 6.43/1.21    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 6.43/1.21  fof(f3833,plain,(
% 6.43/1.21    k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))),
% 6.43/1.21    inference(subsumption_resolution,[],[f3832,f91])).
% 6.43/1.21  fof(f3832,plain,(
% 6.43/1.21    ~r1_tarski(k1_xboole_0,k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))),
% 6.43/1.21    inference(forward_demodulation,[],[f3831,f842])).
% 6.43/1.21  fof(f3831,plain,(
% 6.43/1.21    ~r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))),
% 6.43/1.21    inference(subsumption_resolution,[],[f3830,f86])).
% 6.43/1.21  fof(f3830,plain,(
% 6.43/1.21    ~r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 6.43/1.21    inference(subsumption_resolution,[],[f3801,f85])).
% 6.43/1.21  fof(f3801,plain,(
% 6.43/1.21    ~r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2))) | ~v1_relat_1(sK1) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 6.43/1.21    inference(superposition,[],[f278,f3760])).
% 6.43/1.21  fof(f3760,plain,(
% 6.43/1.21    k1_xboole_0 = k6_subset_1(sK1,sK2)),
% 6.43/1.21    inference(resolution,[],[f3717,f177])).
% 6.43/1.21  fof(f3717,plain,(
% 6.43/1.21    ( ! [X70] : (r1_tarski(k6_subset_1(sK1,sK2),X70)) )),
% 6.43/1.21    inference(resolution,[],[f819,f207])).
% 6.43/1.21  fof(f207,plain,(
% 6.43/1.21    ( ! [X1] : (r1_tarski(k6_subset_1(sK1,X1),sK2)) )),
% 6.43/1.21    inference(resolution,[],[f191,f142])).
% 6.43/1.21  fof(f142,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 6.43/1.21    inference(definition_unfolding,[],[f103,f106])).
% 6.43/1.21  fof(f103,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f9])).
% 6.43/1.21  fof(f9,axiom,(
% 6.43/1.21    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.43/1.21  fof(f191,plain,(
% 6.43/1.21    ( ! [X13] : (~r1_tarski(X13,sK1) | r1_tarski(X13,sK2)) )),
% 6.43/1.21    inference(resolution,[],[f133,f87])).
% 6.43/1.21  fof(f87,plain,(
% 6.43/1.21    r1_tarski(sK1,sK2)),
% 6.43/1.21    inference(cnf_transformation,[],[f61])).
% 6.43/1.21  fof(f133,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f54])).
% 6.43/1.21  fof(f54,plain,(
% 6.43/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.43/1.21    inference(flattening,[],[f53])).
% 6.43/1.21  fof(f53,plain,(
% 6.43/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.43/1.21    inference(ennf_transformation,[],[f7])).
% 6.43/1.21  fof(f7,axiom,(
% 6.43/1.21    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 6.43/1.21  fof(f819,plain,(
% 6.43/1.21    ( ! [X6,X7,X5] : (~r1_tarski(k6_subset_1(X5,X7),X6) | r1_tarski(k6_subset_1(X5,X6),X7)) )),
% 6.43/1.21    inference(resolution,[],[f262,f148])).
% 6.43/1.21  fof(f262,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k2_enumset1(X1,X1,X1,X0))) | r1_tarski(k6_subset_1(X2,X0),X1)) )),
% 6.43/1.21    inference(superposition,[],[f147,f144])).
% 6.43/1.21  fof(f144,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 6.43/1.21    inference(definition_unfolding,[],[f105,f135,f135])).
% 6.43/1.21  fof(f105,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f18])).
% 6.43/1.21  fof(f18,axiom,(
% 6.43/1.21    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.43/1.21  fof(f147,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 6.43/1.21    inference(definition_unfolding,[],[f131,f106,f137])).
% 6.43/1.21  fof(f131,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.43/1.21    inference(cnf_transformation,[],[f51])).
% 6.43/1.21  fof(f51,plain,(
% 6.43/1.21    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.43/1.21    inference(ennf_transformation,[],[f12])).
% 6.43/1.21  fof(f12,axiom,(
% 6.43/1.21    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 6.43/1.21  fof(f278,plain,(
% 6.43/1.21    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(k6_subset_1(X4,X3)),k6_subset_1(k2_relat_1(X4),k2_relat_1(X3))) | ~v1_relat_1(X4) | k2_relat_1(k6_subset_1(X4,X3)) = k6_subset_1(k2_relat_1(X4),k2_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 6.43/1.21    inference(resolution,[],[f95,f117])).
% 6.43/1.21  fof(f95,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f42])).
% 6.43/1.21  fof(f42,plain,(
% 6.43/1.21    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.43/1.21    inference(ennf_transformation,[],[f31])).
% 6.43/1.21  fof(f31,axiom,(
% 6.43/1.21    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 6.43/1.21  fof(f691,plain,(
% 6.43/1.21    ( ! [X19,X17,X18] : (r1_tarski(k6_subset_1(k6_subset_1(X18,k6_subset_1(X18,X17)),X19),X17)) )),
% 6.43/1.21    inference(forward_demodulation,[],[f677,f145])).
% 6.43/1.21  fof(f145,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.43/1.21    inference(definition_unfolding,[],[f110,f136,f106,f106])).
% 6.43/1.21  fof(f136,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 6.43/1.21    inference(definition_unfolding,[],[f107,f135])).
% 6.43/1.21  fof(f107,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.43/1.21    inference(cnf_transformation,[],[f25])).
% 6.43/1.21  fof(f25,axiom,(
% 6.43/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.43/1.21  fof(f110,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.43/1.21    inference(cnf_transformation,[],[f14])).
% 6.43/1.21  fof(f14,axiom,(
% 6.43/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.43/1.21  fof(f677,plain,(
% 6.43/1.21    ( ! [X19,X17,X18] : (r1_tarski(k6_subset_1(k1_setfam_1(k2_enumset1(X18,X18,X18,X17)),X19),X17)) )),
% 6.43/1.21    inference(superposition,[],[f299,f237])).
% 6.43/1.21  fof(f237,plain,(
% 6.43/1.21    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.43/1.21    inference(superposition,[],[f145,f144])).
% 6.43/1.21  fof(f299,plain,(
% 6.43/1.21    ( ! [X10,X11,X9] : (r1_tarski(k6_subset_1(k6_subset_1(X9,X10),X11),X9)) )),
% 6.43/1.21    inference(superposition,[],[f142,f146])).
% 6.43/1.21  fof(f146,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 6.43/1.21    inference(definition_unfolding,[],[f130,f106,f106,f106,f137])).
% 6.43/1.21  fof(f130,plain,(
% 6.43/1.21    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 6.43/1.21    inference(cnf_transformation,[],[f11])).
% 6.43/1.21  fof(f11,axiom,(
% 6.43/1.21    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 6.43/1.21  fof(f88,plain,(
% 6.43/1.21    ~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))),
% 6.43/1.21    inference(cnf_transformation,[],[f61])).
% 6.43/1.21  fof(f5061,plain,(
% 6.43/1.21    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2))),
% 6.43/1.21    inference(subsumption_resolution,[],[f5047,f86])).
% 6.43/1.21  fof(f5047,plain,(
% 6.43/1.21    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 6.43/1.21    inference(resolution,[],[f4975,f386])).
% 6.43/1.21  fof(f386,plain,(
% 6.43/1.21    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(X0)) | r1_tarski(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.43/1.21    inference(resolution,[],[f343,f133])).
% 6.43/1.21  fof(f343,plain,(
% 6.43/1.21    ( ! [X8] : (r1_tarski(k1_relat_1(X8),k3_relat_1(X8)) | ~v1_relat_1(X8)) )),
% 6.43/1.21    inference(superposition,[],[f141,f139])).
% 6.43/1.21  fof(f141,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 6.43/1.21    inference(definition_unfolding,[],[f102,f137])).
% 6.43/1.21  fof(f102,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.43/1.21    inference(cnf_transformation,[],[f16])).
% 6.43/1.21  fof(f16,axiom,(
% 6.43/1.21    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.43/1.21  fof(f4975,plain,(
% 6.43/1.21    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))),
% 6.43/1.21    inference(forward_demodulation,[],[f4953,f138])).
% 6.43/1.21  fof(f4953,plain,(
% 6.43/1.21    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_xboole_0),k1_relat_1(sK2))),
% 6.43/1.21    inference(resolution,[],[f3829,f819])).
% 6.43/1.21  fof(f3829,plain,(
% 6.43/1.21    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_xboole_0)),
% 6.43/1.21    inference(forward_demodulation,[],[f3828,f700])).
% 6.43/1.21  fof(f700,plain,(
% 6.43/1.21    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.43/1.21    inference(resolution,[],[f633,f177])).
% 6.43/1.21  fof(f633,plain,(
% 6.43/1.21    ( ! [X10] : (r1_tarski(k1_relat_1(k1_xboole_0),X10)) )),
% 6.43/1.21    inference(resolution,[],[f600,f119])).
% 6.43/1.21  fof(f3828,plain,(
% 6.43/1.21    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0))),
% 6.43/1.21    inference(subsumption_resolution,[],[f3827,f85])).
% 6.43/1.21  fof(f3827,plain,(
% 6.43/1.21    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1)),
% 6.43/1.21    inference(subsumption_resolution,[],[f3793,f86])).
% 6.43/1.21  fof(f3793,plain,(
% 6.43/1.21    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1)),
% 6.43/1.21    inference(superposition,[],[f96,f3760])).
% 6.43/1.21  fof(f96,plain,(
% 6.43/1.21    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.43/1.21    inference(cnf_transformation,[],[f43])).
% 6.43/1.21  fof(f43,plain,(
% 6.43/1.21    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.43/1.21    inference(ennf_transformation,[],[f29])).
% 6.43/1.21  fof(f29,axiom,(
% 6.43/1.21    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 6.43/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 6.43/1.21  fof(f85,plain,(
% 6.43/1.21    v1_relat_1(sK1)),
% 6.43/1.21    inference(cnf_transformation,[],[f61])).
% 6.43/1.21  % SZS output end Proof for theBenchmark
% 6.43/1.21  % (5818)------------------------------
% 6.43/1.21  % (5818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.43/1.21  % (5818)Termination reason: Refutation
% 6.43/1.21  
% 6.43/1.21  % (5818)Memory used [KB]: 7803
% 6.43/1.21  % (5818)Time elapsed: 0.780 s
% 6.43/1.21  % (5818)------------------------------
% 6.43/1.21  % (5818)------------------------------
% 6.43/1.21  % (5788)Success in time 0.85 s
%------------------------------------------------------------------------------
