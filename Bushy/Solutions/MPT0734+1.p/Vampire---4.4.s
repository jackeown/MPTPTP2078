%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t22_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 122 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 619 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f219,f225,f249])).

fof(f249,plain,(
    ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f233,f67])).

fof(f67,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1)
    & v1_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X0,X2)
            & r2_hidden(sK1,X2)
            & r1_tarski(X0,sK1)
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,X2)
          & r2_hidden(X1,X2)
          & r1_tarski(X0,X1)
          & v3_ordinal1(X2) )
     => ( ~ r2_hidden(X0,sK2)
        & r2_hidden(X1,sK2)
        & r1_tarski(X0,X1)
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',t22_ordinal1)).

fof(f233,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f218,f103])).

fof(f103,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',t7_ordinal1)).

fof(f218,plain,
    ( sK0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_14
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f225,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f223,f64])).

fof(f64,plain,(
    v1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f223,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f222,f66])).

fof(f66,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f222,plain,
    ( ~ v3_ordinal1(sK2)
    | ~ v1_ordinal1(sK0)
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f220,f69])).

fof(f69,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f220,plain,
    ( r2_hidden(sK0,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v1_ordinal1(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f215,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',t21_ordinal1)).

fof(f215,plain,
    ( r2_xboole_0(sK0,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_12
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f219,plain,
    ( spl6_12
    | spl6_14 ),
    inference(avatar_split_clause,[],[f212,f217,f214])).

fof(f212,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f208,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',d8_xboole_0)).

fof(f208,plain,(
    r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f153,f67])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f109,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',t1_xboole_1)).

fof(f109,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f94,plain,(
    v1_ordinal1(sK2) ),
    inference(resolution,[],[f73,f66])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',cc1_ordinal1)).

fof(f107,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v1_ordinal1(sK2) ),
    inference(resolution,[],[f74,f68])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t22_ordinal1.p',d2_ordinal1)).
%------------------------------------------------------------------------------
