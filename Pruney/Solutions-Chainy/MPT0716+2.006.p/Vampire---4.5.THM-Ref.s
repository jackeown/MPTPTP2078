%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:49 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 247 expanded)
%              Number of leaves         :   15 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  349 (1783 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f63,f64,f194,f240,f618])).

fof(f618,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f616,f32])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(f616,plain,
    ( ~ v1_funct_1(sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f615,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f615,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f611,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f611,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(resolution,[],[f610,f208])).

fof(f208,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f207,f31])).

fof(f207,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f197,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(superposition,[],[f52,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f52,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f610,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k10_relat_1(X0,k1_relat_1(sK1)))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | spl3_3 ),
    inference(duplicate_literal_removal,[],[f608])).

fof(f608,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k10_relat_1(X0,k1_relat_1(sK1)))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl3_3 ),
    inference(resolution,[],[f272,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f272,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(k9_relat_1(X7,X8),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X8)
        | ~ r1_tarski(sK0,X7)
        | ~ v1_relat_1(X7) )
    | spl3_3 ),
    inference(subsumption_resolution,[],[f270,f31])).

fof(f270,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(k9_relat_1(X7,X8),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X8)
        | ~ r1_tarski(sK0,X7)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(sK0) )
    | spl3_3 ),
    inference(resolution,[],[f243,f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | spl3_3 ),
    inference(resolution,[],[f61,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f46,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f61,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f240,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f235,f33])).

fof(f235,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_1
    | spl3_2 ),
    inference(resolution,[],[f233,f52])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0)))
        | ~ v1_relat_1(X0) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f228,f31])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0)))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | spl3_2 ),
    inference(resolution,[],[f195,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (22599)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (22608)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (22616)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (22600)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (22624)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (22614)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,X0) )
    | spl3_2 ),
    inference(resolution,[],[f57,f66])).

fof(f57,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f194,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f192,f31])).

fof(f192,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f191,f32])).

fof(f191,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f190,f56])).

fof(f56,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f190,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f187,f60])).

fof(f60,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f187,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f47,f146])).

fof(f146,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f145,f31])).

fof(f145,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f139,f33])).

fof(f139,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f53,f39])).

fof(f53,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f64,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f55,f51])).

fof(f35,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f36,f59,f51])).

fof(f36,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f59,f55,f51])).

fof(f37,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (22603)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (22611)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (22617)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (22619)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (22604)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (22609)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (22601)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (22620)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (22610)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (22612)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (22615)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (22602)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (22607)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (22605)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (22623)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (22621)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.56  % (22613)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.57  % (22618)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.69/0.59  % (22603)Refutation found. Thanks to Tanya!
% 1.69/0.59  % SZS status Theorem for theBenchmark
% 1.81/0.60  % SZS output start Proof for theBenchmark
% 1.81/0.60  fof(f619,plain,(
% 1.81/0.60    $false),
% 1.81/0.60    inference(avatar_sat_refutation,[],[f62,f63,f64,f194,f240,f618])).
% 1.81/0.60  fof(f618,plain,(
% 1.81/0.60    ~spl3_1 | spl3_3),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f617])).
% 1.81/0.60  fof(f617,plain,(
% 1.81/0.60    $false | (~spl3_1 | spl3_3)),
% 1.81/0.60    inference(subsumption_resolution,[],[f616,f32])).
% 1.81/0.60  fof(f32,plain,(
% 1.81/0.60    v1_funct_1(sK0)),
% 1.81/0.60    inference(cnf_transformation,[],[f28])).
% 1.81/0.60  fof(f28,plain,(
% 1.81/0.60    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.81/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 1.81/0.60  fof(f25,plain,(
% 1.81/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.81/0.60    introduced(choice_axiom,[])).
% 1.81/0.60  fof(f26,plain,(
% 1.81/0.60    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.81/0.60    introduced(choice_axiom,[])).
% 1.81/0.60  fof(f27,plain,(
% 1.81/0.60    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 1.81/0.60    introduced(choice_axiom,[])).
% 1.81/0.60  fof(f24,plain,(
% 1.81/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.81/0.60    inference(flattening,[],[f23])).
% 1.81/0.60  fof(f23,plain,(
% 1.81/0.60    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.81/0.60    inference(nnf_transformation,[],[f12])).
% 1.81/0.60  fof(f12,plain,(
% 1.81/0.60    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.81/0.60    inference(flattening,[],[f11])).
% 1.81/0.60  fof(f11,plain,(
% 1.81/0.60    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.81/0.60    inference(ennf_transformation,[],[f10])).
% 1.81/0.60  fof(f10,negated_conjecture,(
% 1.81/0.60    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.81/0.60    inference(negated_conjecture,[],[f9])).
% 1.81/0.60  fof(f9,conjecture,(
% 1.81/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).
% 1.81/0.60  fof(f616,plain,(
% 1.81/0.60    ~v1_funct_1(sK0) | (~spl3_1 | spl3_3)),
% 1.81/0.60    inference(subsumption_resolution,[],[f615,f31])).
% 1.81/0.60  fof(f31,plain,(
% 1.81/0.60    v1_relat_1(sK0)),
% 1.81/0.60    inference(cnf_transformation,[],[f28])).
% 1.81/0.60  fof(f615,plain,(
% 1.81/0.60    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | (~spl3_1 | spl3_3)),
% 1.81/0.60    inference(subsumption_resolution,[],[f611,f48])).
% 1.81/0.60  fof(f48,plain,(
% 1.81/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.81/0.60    inference(equality_resolution,[],[f43])).
% 1.81/0.60  fof(f43,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.81/0.60    inference(cnf_transformation,[],[f30])).
% 1.81/0.60  fof(f30,plain,(
% 1.81/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.60    inference(flattening,[],[f29])).
% 1.81/0.60  fof(f29,plain,(
% 1.81/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.60    inference(nnf_transformation,[],[f1])).
% 1.81/0.60  fof(f1,axiom,(
% 1.81/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.60  fof(f611,plain,(
% 1.81/0.60    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | (~spl3_1 | spl3_3)),
% 1.81/0.60    inference(resolution,[],[f610,f208])).
% 1.81/0.60  fof(f208,plain,(
% 1.81/0.60    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl3_1),
% 1.81/0.60    inference(subsumption_resolution,[],[f207,f31])).
% 1.81/0.60  fof(f207,plain,(
% 1.81/0.60    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK0) | ~spl3_1),
% 1.81/0.60    inference(subsumption_resolution,[],[f197,f33])).
% 1.81/0.60  fof(f33,plain,(
% 1.81/0.60    v1_relat_1(sK1)),
% 1.81/0.60    inference(cnf_transformation,[],[f28])).
% 1.81/0.60  fof(f197,plain,(
% 1.81/0.60    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl3_1),
% 1.81/0.60    inference(superposition,[],[f52,f39])).
% 1.81/0.60  fof(f39,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f14])).
% 1.81/0.60  fof(f14,plain,(
% 1.81/0.60    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f5])).
% 1.81/0.60  fof(f5,axiom,(
% 1.81/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.81/0.60  fof(f52,plain,(
% 1.81/0.60    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 1.81/0.60    inference(avatar_component_clause,[],[f51])).
% 1.81/0.60  fof(f51,plain,(
% 1.81/0.60    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.81/0.60  fof(f610,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(sK2,k10_relat_1(X0,k1_relat_1(sK1))) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | spl3_3),
% 1.81/0.60    inference(duplicate_literal_removal,[],[f608])).
% 1.81/0.60  fof(f608,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(sK2,k10_relat_1(X0,k1_relat_1(sK1))) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | spl3_3),
% 1.81/0.60    inference(resolution,[],[f272,f41])).
% 1.81/0.60  fof(f41,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f17])).
% 1.81/0.60  fof(f17,plain,(
% 1.81/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(flattening,[],[f16])).
% 1.81/0.60  fof(f16,plain,(
% 1.81/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.81/0.60    inference(ennf_transformation,[],[f7])).
% 1.81/0.60  fof(f7,axiom,(
% 1.81/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.81/0.60  fof(f272,plain,(
% 1.81/0.60    ( ! [X8,X7] : (~r1_tarski(k9_relat_1(X7,X8),k1_relat_1(sK1)) | ~r1_tarski(sK2,X8) | ~r1_tarski(sK0,X7) | ~v1_relat_1(X7)) ) | spl3_3),
% 1.81/0.60    inference(subsumption_resolution,[],[f270,f31])).
% 1.81/0.60  fof(f270,plain,(
% 1.81/0.60    ( ! [X8,X7] : (~r1_tarski(k9_relat_1(X7,X8),k1_relat_1(sK1)) | ~r1_tarski(sK2,X8) | ~r1_tarski(sK0,X7) | ~v1_relat_1(X7) | ~v1_relat_1(sK0)) ) | spl3_3),
% 1.81/0.60    inference(resolution,[],[f243,f45])).
% 1.81/0.60  fof(f45,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f19])).
% 1.81/0.60  fof(f19,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.81/0.60    inference(flattening,[],[f18])).
% 1.81/0.60  fof(f18,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.81/0.60    inference(ennf_transformation,[],[f4])).
% 1.81/0.60  fof(f4,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 1.81/0.60  fof(f243,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(k9_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | spl3_3),
% 1.81/0.60    inference(resolution,[],[f61,f66])).
% 1.81/0.60  fof(f66,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.81/0.60    inference(superposition,[],[f46,f40])).
% 1.81/0.60  fof(f40,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f15])).
% 1.81/0.60  fof(f15,plain,(
% 1.81/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f3])).
% 1.81/0.60  fof(f3,axiom,(
% 1.81/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.81/0.60  fof(f46,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f20])).
% 1.81/0.60  fof(f20,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.81/0.60    inference(ennf_transformation,[],[f2])).
% 1.81/0.60  fof(f2,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.81/0.60  fof(f61,plain,(
% 1.81/0.60    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | spl3_3),
% 1.81/0.60    inference(avatar_component_clause,[],[f59])).
% 1.81/0.60  fof(f59,plain,(
% 1.81/0.60    spl3_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.81/0.60  fof(f240,plain,(
% 1.81/0.60    ~spl3_1 | spl3_2),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f239])).
% 1.81/0.60  fof(f239,plain,(
% 1.81/0.60    $false | (~spl3_1 | spl3_2)),
% 1.81/0.60    inference(subsumption_resolution,[],[f235,f33])).
% 1.81/0.60  fof(f235,plain,(
% 1.81/0.60    ~v1_relat_1(sK1) | (~spl3_1 | spl3_2)),
% 1.81/0.60    inference(resolution,[],[f233,f52])).
% 1.81/0.60  fof(f233,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0))) | ~v1_relat_1(X0)) ) | spl3_2),
% 1.81/0.60    inference(subsumption_resolution,[],[f228,f31])).
% 1.81/0.60  fof(f228,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | spl3_2),
% 1.81/0.60    inference(resolution,[],[f195,f38])).
% 1.81/0.60  fof(f38,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f13])).
% 1.81/0.60  fof(f13,plain,(
% 1.81/0.60    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f6])).
% 1.81/0.60  % (22599)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.81/0.60  % (22608)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.81/0.60  % (22616)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.81/0.60  % (22600)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.81/0.60  % (22624)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.81/0.61  % (22614)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.81/0.61  fof(f195,plain,(
% 1.81/0.61    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(sK2,X0)) ) | spl3_2),
% 1.81/0.61    inference(resolution,[],[f57,f66])).
% 1.81/0.61  fof(f57,plain,(
% 1.81/0.61    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl3_2),
% 1.81/0.61    inference(avatar_component_clause,[],[f55])).
% 1.81/0.61  fof(f55,plain,(
% 1.81/0.61    spl3_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.81/0.61  fof(f194,plain,(
% 1.81/0.61    spl3_1 | ~spl3_2 | ~spl3_3),
% 1.81/0.61    inference(avatar_contradiction_clause,[],[f193])).
% 1.81/0.61  fof(f193,plain,(
% 1.81/0.61    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f192,f31])).
% 1.81/0.61  fof(f192,plain,(
% 1.81/0.61    ~v1_relat_1(sK0) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f191,f32])).
% 1.81/0.61  fof(f191,plain,(
% 1.81/0.61    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f190,f56])).
% 1.81/0.61  fof(f56,plain,(
% 1.81/0.61    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_2),
% 1.81/0.61    inference(avatar_component_clause,[],[f55])).
% 1.81/0.61  fof(f190,plain,(
% 1.81/0.61    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f187,f60])).
% 1.81/0.61  fof(f60,plain,(
% 1.81/0.61    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl3_3),
% 1.81/0.61    inference(avatar_component_clause,[],[f59])).
% 1.81/0.61  fof(f187,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_1),
% 1.81/0.61    inference(resolution,[],[f47,f146])).
% 1.81/0.61  fof(f146,plain,(
% 1.81/0.61    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | spl3_1),
% 1.81/0.61    inference(subsumption_resolution,[],[f145,f31])).
% 1.81/0.61  fof(f145,plain,(
% 1.81/0.61    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK0) | spl3_1),
% 1.81/0.61    inference(subsumption_resolution,[],[f139,f33])).
% 1.81/0.61  fof(f139,plain,(
% 1.81/0.61    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_1),
% 1.81/0.61    inference(superposition,[],[f53,f39])).
% 1.81/0.61  fof(f53,plain,(
% 1.81/0.61    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl3_1),
% 1.81/0.61    inference(avatar_component_clause,[],[f51])).
% 1.81/0.61  fof(f47,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f22])).
% 1.81/0.61  fof(f22,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.81/0.61    inference(flattening,[],[f21])).
% 1.81/0.61  fof(f21,plain,(
% 1.81/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.81/0.61    inference(ennf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 1.81/0.61  fof(f64,plain,(
% 1.81/0.61    spl3_1 | spl3_2),
% 1.81/0.61    inference(avatar_split_clause,[],[f35,f55,f51])).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f28])).
% 1.81/0.61  fof(f63,plain,(
% 1.81/0.61    spl3_1 | spl3_3),
% 1.81/0.61    inference(avatar_split_clause,[],[f36,f59,f51])).
% 1.81/0.61  fof(f36,plain,(
% 1.81/0.61    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f28])).
% 1.81/0.61  fof(f62,plain,(
% 1.81/0.61    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.81/0.61    inference(avatar_split_clause,[],[f37,f59,f55,f51])).
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f28])).
% 1.81/0.61  % SZS output end Proof for theBenchmark
% 1.81/0.61  % (22603)------------------------------
% 1.81/0.61  % (22603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (22603)Termination reason: Refutation
% 1.81/0.61  
% 1.81/0.61  % (22603)Memory used [KB]: 6524
% 1.81/0.61  % (22603)Time elapsed: 0.155 s
% 1.81/0.61  % (22603)------------------------------
% 1.81/0.61  % (22603)------------------------------
% 1.81/0.61  % (22598)Success in time 0.249 s
%------------------------------------------------------------------------------
