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
% DateTime   : Thu Dec  3 12:54:48 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 257 expanded)
%              Number of leaves         :   16 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  333 (1871 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f849,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f91,f508,f550,f848])).

fof(f848,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f847])).

fof(f847,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f846,f49])).

fof(f49,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f846,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f845,f50])).

fof(f50,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f845,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f842,f522])).

fof(f522,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f521,f49])).

fof(f521,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f511,f51])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f511,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(superposition,[],[f79,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f79,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f842,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_3 ),
    inference(resolution,[],[f841,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f841,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X0) )
    | spl3_3 ),
    inference(subsumption_resolution,[],[f840,f49])).

fof(f840,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK0) )
    | spl3_3 ),
    inference(superposition,[],[f837,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f837,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X0) )
    | spl3_3 ),
    inference(subsumption_resolution,[],[f829,f49])).

fof(f829,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK1)) )
    | spl3_3 ),
    inference(resolution,[],[f430,f553])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | spl3_3 ),
    inference(resolution,[],[f88,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f88,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f430,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
      | ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f426,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f426,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f63,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f550,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f545,f51])).

fof(f545,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_1
    | spl3_2 ),
    inference(resolution,[],[f544,f79])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0)))
        | ~ v1_relat_1(X0) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f539,f49])).

fof(f539,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0)))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | spl3_2 ),
    inference(resolution,[],[f509,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f509,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,X0) )
    | spl3_2 ),
    inference(resolution,[],[f84,f73])).

fof(f84,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f508,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f506,f49])).

fof(f506,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f505,f50])).

fof(f505,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f504,f83])).

fof(f83,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f504,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f501,f87])).

fof(f87,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f501,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f72,f374])).

fof(f374,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f373,f49])).

fof(f373,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f366,f51])).

fof(f366,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f80,f58])).

fof(f80,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f91,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f53,f82,f78])).

fof(f53,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f54,f86,f78])).

fof(f54,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f86,f82,f78])).

fof(f55,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (14082)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (14075)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (14070)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14092)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (14093)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (14074)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (14085)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (14087)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (14077)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (14072)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (14088)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (14076)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (14080)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (14094)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (14073)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (14083)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (14071)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (14081)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (14089)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.38/0.53  % (14079)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.53  % (14090)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.38/0.54  % (14074)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % (14078)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.54  % (14084)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.38/0.54  % (14095)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.38/0.55  % (14091)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.38/0.55  % (14086)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f849,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f89,f90,f91,f508,f550,f848])).
% 1.47/0.56  fof(f848,plain,(
% 1.47/0.56    ~spl3_1 | spl3_3),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f847])).
% 1.47/0.56  fof(f847,plain,(
% 1.47/0.56    $false | (~spl3_1 | spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f846,f49])).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    v1_relat_1(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.47/0.56    inference(flattening,[],[f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.47/0.56    inference(nnf_transformation,[],[f21])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.47/0.56    inference(flattening,[],[f20])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,negated_conjecture,(
% 1.47/0.56    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.47/0.56    inference(negated_conjecture,[],[f18])).
% 1.47/0.56  fof(f18,conjecture,(
% 1.47/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 1.47/0.56  fof(f846,plain,(
% 1.47/0.56    ~v1_relat_1(sK0) | (~spl3_1 | spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f845,f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    v1_funct_1(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  fof(f845,plain,(
% 1.47/0.56    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl3_1 | spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f842,f522])).
% 1.47/0.56  fof(f522,plain,(
% 1.47/0.56    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl3_1),
% 1.47/0.56    inference(subsumption_resolution,[],[f521,f49])).
% 1.47/0.56  fof(f521,plain,(
% 1.47/0.56    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK0) | ~spl3_1),
% 1.47/0.56    inference(subsumption_resolution,[],[f511,f51])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    v1_relat_1(sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  fof(f511,plain,(
% 1.47/0.56    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl3_1),
% 1.47/0.56    inference(superposition,[],[f79,f58])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.47/0.56  fof(f79,plain,(
% 1.47/0.56    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f78])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.47/0.56  fof(f842,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_3),
% 1.47/0.56    inference(resolution,[],[f841,f67])).
% 1.47/0.56  fof(f67,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(flattening,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,axiom,(
% 1.47/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.47/0.56  fof(f841,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1)) | ~r1_tarski(sK2,X0)) ) | spl3_3),
% 1.47/0.56    inference(subsumption_resolution,[],[f840,f49])).
% 1.47/0.56  fof(f840,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(sK0)) ) | spl3_3),
% 1.47/0.56    inference(superposition,[],[f837,f64])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.47/0.56  fof(f837,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK1)) | ~r1_tarski(sK2,X0)) ) | spl3_3),
% 1.47/0.56    inference(subsumption_resolution,[],[f829,f49])).
% 1.47/0.56  fof(f829,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK1))) ) | spl3_3),
% 1.47/0.56    inference(resolution,[],[f430,f553])).
% 1.47/0.56  fof(f553,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k9_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | spl3_3),
% 1.47/0.56    inference(resolution,[],[f88,f73])).
% 1.47/0.56  fof(f73,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f38])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(flattening,[],[f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.47/0.56  fof(f88,plain,(
% 1.47/0.56    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | spl3_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f86])).
% 1.47/0.56  fof(f86,plain,(
% 1.47/0.56    spl3_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.47/0.56  fof(f430,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1))) | ~r1_tarski(X2,X1) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f426,f62])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.47/0.56  fof(f426,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1))) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X2,X1) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(superposition,[],[f63,f59])).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.47/0.56  fof(f550,plain,(
% 1.47/0.56    ~spl3_1 | spl3_2),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f549])).
% 1.47/0.56  fof(f549,plain,(
% 1.47/0.56    $false | (~spl3_1 | spl3_2)),
% 1.47/0.56    inference(subsumption_resolution,[],[f545,f51])).
% 1.47/0.56  fof(f545,plain,(
% 1.47/0.56    ~v1_relat_1(sK1) | (~spl3_1 | spl3_2)),
% 1.47/0.56    inference(resolution,[],[f544,f79])).
% 1.47/0.56  fof(f544,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0))) | ~v1_relat_1(X0)) ) | spl3_2),
% 1.47/0.56    inference(subsumption_resolution,[],[f539,f49])).
% 1.47/0.56  fof(f539,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | spl3_2),
% 1.47/0.56    inference(resolution,[],[f509,f57])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,axiom,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.47/0.56  fof(f509,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(sK2,X0)) ) | spl3_2),
% 1.47/0.56    inference(resolution,[],[f84,f73])).
% 1.47/0.56  fof(f84,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl3_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f82])).
% 1.47/0.56  fof(f82,plain,(
% 1.47/0.56    spl3_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.47/0.56  fof(f508,plain,(
% 1.47/0.56    spl3_1 | ~spl3_2 | ~spl3_3),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f507])).
% 1.47/0.56  fof(f507,plain,(
% 1.47/0.56    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f506,f49])).
% 1.47/0.56  fof(f506,plain,(
% 1.47/0.56    ~v1_relat_1(sK0) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f505,f50])).
% 1.47/0.56  fof(f505,plain,(
% 1.47/0.56    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f504,f83])).
% 1.47/0.56  fof(f83,plain,(
% 1.47/0.56    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f82])).
% 1.47/0.56  fof(f504,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_3)),
% 1.47/0.56    inference(subsumption_resolution,[],[f501,f87])).
% 1.47/0.56  fof(f87,plain,(
% 1.47/0.56    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl3_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f86])).
% 1.47/0.56  fof(f501,plain,(
% 1.47/0.56    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_1),
% 1.47/0.56    inference(resolution,[],[f72,f374])).
% 1.47/0.56  fof(f374,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | spl3_1),
% 1.47/0.56    inference(subsumption_resolution,[],[f373,f49])).
% 1.47/0.56  fof(f373,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK0) | spl3_1),
% 1.47/0.56    inference(subsumption_resolution,[],[f366,f51])).
% 1.47/0.56  fof(f366,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_1),
% 1.47/0.56    inference(superposition,[],[f80,f58])).
% 1.47/0.56  fof(f80,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl3_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f78])).
% 1.47/0.56  fof(f72,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f36])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.47/0.56    inference(flattening,[],[f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.47/0.56  fof(f91,plain,(
% 1.47/0.56    spl3_1 | spl3_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f53,f82,f78])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  fof(f90,plain,(
% 1.47/0.56    spl3_1 | spl3_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f54,f86,f78])).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  fof(f89,plain,(
% 1.47/0.56    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f55,f86,f82,f78])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (14074)------------------------------
% 1.47/0.56  % (14074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (14074)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (14074)Memory used [KB]: 6524
% 1.47/0.56  % (14074)Time elapsed: 0.114 s
% 1.47/0.56  % (14074)------------------------------
% 1.47/0.56  % (14074)------------------------------
% 1.47/0.56  % (14069)Success in time 0.195 s
%------------------------------------------------------------------------------
