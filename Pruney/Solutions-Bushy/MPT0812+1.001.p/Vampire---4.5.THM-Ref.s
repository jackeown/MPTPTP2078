%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0812+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 175 expanded)
%              Number of leaves         :    8 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  178 ( 865 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f22,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v2_wellord1(sK3)
    & v2_wellord1(sK2)
    & r4_wellord1(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(X1)
            & v2_wellord1(X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(sK2)
          & r4_wellord1(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ~ v2_wellord1(X1)
        & v2_wellord1(sK2)
        & r4_wellord1(sK2,X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(sK3)
      & v2_wellord1(sK2)
      & r4_wellord1(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( v2_wellord1(X0)
                & r4_wellord1(X0,X1) )
             => v2_wellord1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( v2_wellord1(X0)
              & r4_wellord1(X0,X1) )
           => v2_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_wellord1)).

fof(f57,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f25,plain,(
    ~ v2_wellord1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( v2_wellord1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    r3_wellord1(sK2,sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f43,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r3_wellord1(X1,X0,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r3_wellord1(X1,X0,X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ( r3_wellord1(X1,X0,sK4(X0,X1))
          & v1_funct_1(sK4(X0,X1))
          & v1_relat_1(sK4(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X1,X0,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X1,X0,sK4(X0,X1))
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r3_wellord1(X1,X0,X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ? [X3] :
            ( r3_wellord1(X1,X0,X3)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ! [X2] :
            ( ~ r3_wellord1(X0,X1,X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ? [X2] :
            ( r3_wellord1(X0,X1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ? [X2] :
          ( r3_wellord1(X0,X1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f43,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f42,plain,
    ( ~ v1_relat_1(sK3)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    r4_wellord1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r4_wellord1(sK2,X0)
      | ~ v1_relat_1(X0)
      | sP0(X0,sK2) ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r4_wellord1(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( r4_wellord1(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ r4_wellord1(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r4_wellord1(X0,X1)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f7,f11,f10])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK2,X0,sK4(sK3,sK2))
      | v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f54,f44])).

fof(f44,plain,(
    v1_relat_1(sK4(sK3,sK2)) ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_relat_1(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ r3_wellord1(sK2,X0,sK4(sK3,sK2))
      | ~ v1_relat_1(sK4(sK3,sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    v1_funct_1(sK4(sK3,sK2)) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_1(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | v2_wellord1(X0)
      | ~ r3_wellord1(sK2,X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f36,f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(sK2,X0,X1)
      | v2_wellord1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | v2_wellord1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_wellord1)).

fof(f24,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
