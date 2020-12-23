%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 286 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   26
%              Number of atoms          :  468 (1499 expanded)
%              Number of equality atoms :  183 ( 625 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f99,f109,f118,f282])).

fof(f282,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f74,f117,f271,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f271,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(subsumption_resolution,[],[f270,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k2_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f74,f147])).

fof(f147,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f146,f89])).

fof(f89,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f146,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f144,f84])).

fof(f84,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f144,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f64,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f70,f54])).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f136,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f135,f89])).

fof(f135,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f134,f84])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2 ),
    inference(superposition,[],[f65,f79])).

fof(f79,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_2
  <=> k1_tarski(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f65,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f64,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f270,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k2_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(equality_resolution,[],[f265])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | k1_tarski(X0) = k2_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(subsumption_resolution,[],[f263,f117])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | k1_xboole_0 = k2_relat_1(sK1)
        | k1_tarski(X0) = k2_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | k1_xboole_0 = k2_relat_1(sK1)
        | k1_tarski(X0) = k2_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | k1_tarski(X0) = k2_relat_1(sK1) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(superposition,[],[f58,f175])).

fof(f175,plain,
    ( ! [X6,X5] :
        ( sK6(k2_relat_1(sK1),X6) = X5
        | ~ r2_hidden(X5,k2_relat_1(sK1))
        | k2_relat_1(sK1) = k1_tarski(X6) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(subsumption_resolution,[],[f171,f117])).

fof(f171,plain,
    ( ! [X6,X5] :
        ( sK6(k2_relat_1(sK1),X6) = X5
        | ~ r2_hidden(X5,k2_relat_1(sK1))
        | k1_xboole_0 = k2_relat_1(sK1)
        | k2_relat_1(sK1) = k1_tarski(X6) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f157,f57])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | X0 = X1
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f147,f147])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f117,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_7
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f74,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_1
  <=> k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f118,plain,
    ( ~ spl7_7
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f113,f104,f87,f77,f115])).

fof(f104,plain,
    ( spl7_6
  <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f113,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f112,f91])).

fof(f91,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f69,f54])).

fof(f69,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f112,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f111,f79])).

fof(f111,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f110,f89])).

fof(f110,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_6 ),
    inference(superposition,[],[f55,f106])).

fof(f106,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f109,plain,
    ( spl7_6
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f108,f96,f87,f104])).

fof(f96,plain,
    ( spl7_5
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f108,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f101,f89])).

fof(f101,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl7_5 ),
    inference(superposition,[],[f59,f98])).

fof(f98,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f99,plain,
    ( spl7_5
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f94,f87,f77,f96])).

fof(f94,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f93,f89])).

fof(f93,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(superposition,[],[f47,f79])).

fof(f47,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f90,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f85,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:16:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (9609)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (9625)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (9630)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (9614)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (9617)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (9604)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (9601)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (9605)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (9628)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (9603)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (9623)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (9630)Refutation not found, incomplete strategy% (9630)------------------------------
% 0.22/0.56  % (9630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9630)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9630)Memory used [KB]: 1663
% 0.22/0.56  % (9630)Time elapsed: 0.139 s
% 0.22/0.56  % (9630)------------------------------
% 0.22/0.56  % (9630)------------------------------
% 0.22/0.56  % (9616)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (9618)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (9610)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (9622)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (9626)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (9619)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (9612)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (9606)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (9615)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (9624)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (9617)Refutation not found, incomplete strategy% (9617)------------------------------
% 0.22/0.56  % (9617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9617)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9617)Memory used [KB]: 10618
% 0.22/0.56  % (9617)Time elapsed: 0.134 s
% 0.22/0.56  % (9617)------------------------------
% 0.22/0.56  % (9617)------------------------------
% 0.22/0.57  % (9622)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (9620)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (9627)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (9607)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (9608)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (9613)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (9602)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (9629)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (9621)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.58  % (9611)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f289,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f99,f109,f118,f282])).
% 0.22/0.58  fof(f282,plain,(
% 0.22/0.58    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f276])).
% 0.22/0.58  fof(f276,plain,(
% 0.22/0.58    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f74,f117,f271,f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0,X1] : ((sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.58  fof(f271,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f270,f158])).
% 0.22/0.58  fof(f158,plain,(
% 0.22/0.58    ( ! [X0] : (k1_tarski(X0) != k2_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(superposition,[],[f74,f147])).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f146,f89])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    v1_relat_1(sK1) | ~spl7_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f87])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    spl7_4 <=> v1_relat_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.58  fof(f146,plain,(
% 0.22/0.58    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f144,f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    v1_funct_1(sK1) | ~spl7_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f82])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    spl7_3 <=> v1_funct_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.58  fof(f144,plain,(
% 0.22/0.58    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f141])).
% 0.22/0.58  fof(f141,plain,(
% 0.22/0.58    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(superposition,[],[f64,f139])).
% 0.22/0.58  fof(f139,plain,(
% 0.22/0.58    ( ! [X0] : (sK0 = sK4(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(resolution,[],[f136,f130])).
% 0.22/0.58  fof(f130,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f129])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.22/0.58    inference(superposition,[],[f70,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.58    inference(equality_resolution,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.58    inference(rectify,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.58    inference(flattening,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f135,f89])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl7_2 | ~spl7_3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f134,f84])).
% 0.22/0.58  fof(f134,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl7_2),
% 0.22/0.58    inference(superposition,[],[f65,f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    k1_tarski(sK0) = k1_relat_1(sK1) | ~spl7_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f77])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    spl7_2 <=> k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(rectify,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f270,plain,(
% 0.22/0.58    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(equality_resolution,[],[f265])).
% 0.22/0.58  fof(f265,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) = k2_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f263,f117])).
% 0.22/0.58  fof(f263,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X0) = k2_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f260])).
% 0.22/0.58  fof(f260,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X0) = k2_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | k1_tarski(X0) = k2_relat_1(sK1)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(superposition,[],[f58,f175])).
% 0.22/0.58  fof(f175,plain,(
% 0.22/0.58    ( ! [X6,X5] : (sK6(k2_relat_1(sK1),X6) = X5 | ~r2_hidden(X5,k2_relat_1(sK1)) | k2_relat_1(sK1) = k1_tarski(X6)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f171,f117])).
% 0.22/0.58  fof(f171,plain,(
% 0.22/0.58    ( ! [X6,X5] : (sK6(k2_relat_1(sK1),X6) = X5 | ~r2_hidden(X5,k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k1_tarski(X6)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(resolution,[],[f157,f57])).
% 0.22/0.58  fof(f157,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | X0 = X1 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.58    inference(superposition,[],[f147,f147])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0,X1] : (sK6(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    k1_xboole_0 != k2_relat_1(sK1) | spl7_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f115])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    spl7_7 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) | spl7_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f72])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    spl7_1 <=> k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.58  fof(f118,plain,(
% 0.22/0.58    ~spl7_7 | ~spl7_2 | ~spl7_4 | ~spl7_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f113,f104,f87,f77,f115])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    spl7_6 <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.58  fof(f113,plain,(
% 0.22/0.58    k1_xboole_0 != k2_relat_1(sK1) | (~spl7_2 | ~spl7_4 | ~spl7_6)),
% 0.22/0.58    inference(subsumption_resolution,[],[f112,f91])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.22/0.58    inference(superposition,[],[f69,f54])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.22/0.58    inference(equality_resolution,[],[f68])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.22/0.58    inference(equality_resolution,[],[f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f112,plain,(
% 0.22/0.58    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 != k2_relat_1(sK1) | (~spl7_2 | ~spl7_4 | ~spl7_6)),
% 0.22/0.58    inference(forward_demodulation,[],[f111,f79])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | (~spl7_4 | ~spl7_6)),
% 0.22/0.58    inference(subsumption_resolution,[],[f110,f89])).
% 0.22/0.58  fof(f110,plain,(
% 0.22/0.58    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl7_6),
% 0.22/0.58    inference(superposition,[],[f55,f106])).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~spl7_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f104])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.58  fof(f109,plain,(
% 0.22/0.58    spl7_6 | ~spl7_4 | ~spl7_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f108,f96,f87,f104])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    spl7_5 <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.58  fof(f108,plain,(
% 0.22/0.58    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | (~spl7_4 | ~spl7_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f101,f89])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl7_5),
% 0.22/0.58    inference(superposition,[],[f59,f98])).
% 0.22/0.58  fof(f98,plain,(
% 0.22/0.58    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) | ~spl7_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f96])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    spl7_5 | ~spl7_2 | ~spl7_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f94,f87,f77,f96])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) | (~spl7_2 | ~spl7_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f93,f89])).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl7_2),
% 0.22/0.58    inference(superposition,[],[f47,f79])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    spl7_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f37,f87])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    v1_relat_1(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.58    inference(negated_conjecture,[],[f11])).
% 0.22/0.58  fof(f11,conjecture,(
% 0.22/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    spl7_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f38,f82])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    v1_funct_1(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    spl7_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f39,f77])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    ~spl7_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f40,f72])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (9622)------------------------------
% 0.22/0.58  % (9622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (9622)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (9622)Memory used [KB]: 6396
% 0.22/0.58  % (9622)Time elapsed: 0.144 s
% 0.22/0.58  % (9622)------------------------------
% 0.22/0.58  % (9622)------------------------------
% 0.22/0.58  % (9600)Success in time 0.212 s
%------------------------------------------------------------------------------
