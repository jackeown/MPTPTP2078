%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0441+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 409 expanded)
%              Number of leaves         :   15 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :  307 (2466 expanded)
%              Number of equality atoms :  139 (1485 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f723,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f385,f722])).

fof(f722,plain,(
    spl12_2 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl12_2 ),
    inference(subsumption_resolution,[],[f718,f423])).

fof(f423,plain,
    ( r2_hidden(sK11(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f65,f395,f396,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X2)
      | sK11(X0,X1,X2) = X1
      | sK11(X0,X1,X2) = X0
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK11(X0,X1,X2) != X1
              & sK11(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sK11(X0,X1,X2) = X1
            | sK11(X0,X1,X2) = X0
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK11(X0,X1,X2) != X1
            & sK11(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sK11(X0,X1,X2) = X1
          | sK11(X0,X1,X2) = X0
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f396,plain,
    ( sK3 != sK11(sK1,sK3,k2_relat_1(sK4))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f69,f65,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sK11(X0,X1,X2) != X1
      | k2_tarski(X0,X1) = X2
      | ~ r2_hidden(X1,X2) ) ),
    inference(inner_rewriting,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK11(X0,X1,X2) != X1
      | ~ r2_hidden(sK11(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f67,f47])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f67,plain,(
    r2_hidden(k4_tarski(sK2,sK3),sK4) ),
    inference(superposition,[],[f52,f29])).

fof(f29,plain,(
    sK4 = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k2_relat_1(sK4) != k2_tarski(sK1,sK3)
      | k1_relat_1(sK4) != k2_tarski(sK0,sK2) )
    & sK4 = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( k2_relat_1(X4) != k2_tarski(X1,X3)
          | k1_relat_1(X4) != k2_tarski(X0,X2) )
        & k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 )
   => ( ( k2_relat_1(sK4) != k2_tarski(sK1,sK3)
        | k1_relat_1(sK4) != k2_tarski(sK0,sK2) )
      & sK4 = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) != k2_tarski(X1,X3)
        | k1_relat_1(X4) != k2_tarski(X0,X2) )
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( v1_relat_1(X4)
       => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
         => ( k2_relat_1(X4) = k2_tarski(X1,X3)
            & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

fof(f52,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f395,plain,
    ( sK1 != sK11(sK1,sK3,k2_relat_1(sK4))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f70,f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sK11(X0,X1,X2) != X0
      | k2_tarski(X0,X1) = X2
      | ~ r2_hidden(X0,X2) ) ),
    inference(inner_rewriting,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK11(X0,X1,X2) != X0
      | ~ r2_hidden(sK11(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    r2_hidden(sK1,k2_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f68,f47])).

fof(f68,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK4) ),
    inference(superposition,[],[f54,f29])).

fof(f54,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,
    ( k2_relat_1(sK4) != k2_tarski(sK1,sK3)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl12_2
  <=> k2_relat_1(sK4) = k2_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f718,plain,
    ( ~ r2_hidden(sK11(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f637,f48])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f637,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK11(sK1,sK3,k2_relat_1(sK4))),sK4)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f407,f421,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | k4_tarski(sK0,sK1) = X0
      | k4_tarski(sK2,sK3) = X0 ) ),
    inference(superposition,[],[f55,f29])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f421,plain,
    ( ! [X0,X1] : k4_tarski(X0,sK11(sK1,sK3,k2_relat_1(sK4))) != k4_tarski(X1,sK3)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f396,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X2,X3) != k4_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k4_tarski(X0,X1)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f407,plain,
    ( ! [X0,X1] : k4_tarski(X0,sK11(sK1,sK3,k2_relat_1(sK4))) != k4_tarski(X1,sK1)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f395,f46])).

fof(f385,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f381,f128])).

fof(f128,plain,
    ( r2_hidden(sK11(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f61,f99,f101,f42])).

fof(f101,plain,
    ( sK0 != sK11(sK0,sK2,k1_relat_1(sK4))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f74,f61,f57])).

fof(f74,plain,(
    r2_hidden(sK0,k1_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f19,f22,f21,f20])).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f99,plain,
    ( sK2 != sK11(sK0,sK2,k1_relat_1(sK4))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f73,f61,f56])).

fof(f73,plain,(
    r2_hidden(sK2,k1_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f67,f49])).

fof(f61,plain,
    ( k1_relat_1(sK4) != k2_tarski(sK0,sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl12_1
  <=> k1_relat_1(sK4) = k2_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f381,plain,
    ( ~ r2_hidden(sK11(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f356,f50])).

fof(f50,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f356,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK11(sK0,sK2,k1_relat_1(sK4)),X0),sK4)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f113,f127,f96])).

fof(f127,plain,
    ( ! [X0,X1] : k4_tarski(sK11(sK0,sK2,k1_relat_1(sK4)),X0) != k4_tarski(sK0,X1)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f101,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f113,plain,
    ( ! [X0,X1] : k4_tarski(sK11(sK0,sK2,k1_relat_1(sK4)),X0) != k4_tarski(sK2,X1)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f99,f45])).

fof(f66,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f30,f63,f59])).

fof(f30,plain,
    ( k2_relat_1(sK4) != k2_tarski(sK1,sK3)
    | k1_relat_1(sK4) != k2_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
