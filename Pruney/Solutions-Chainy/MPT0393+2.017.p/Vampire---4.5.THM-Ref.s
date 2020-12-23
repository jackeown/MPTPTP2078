%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:53 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   69 (1281 expanded)
%              Number of leaves         :   11 ( 382 expanded)
%              Depth                    :   29
%              Number of atoms          :  292 (7929 expanded)
%              Number of equality atoms :  133 (3640 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f335,f314])).

fof(f314,plain,(
    ! [X0,X3] : X0 = X3 ),
    inference(subsumption_resolution,[],[f229,f228])).

fof(f228,plain,(
    ! [X3] : r2_hidden(X3,sK0) ),
    inference(backward_demodulation,[],[f65,f224])).

fof(f224,plain,(
    ! [X6] : sK0 = X6 ),
    inference(subsumption_resolution,[],[f220,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f220,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_xboole_0,k1_tarski(X6))
      | sK0 = X6 ) ),
    inference(resolution,[],[f169,f66])).

fof(f66,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f161,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f161,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f65,f142])).

fof(f142,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f141,f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f35,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).

fof(f15,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f125,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f41,f118])).

fof(f118,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f117,f96])).

fof(f96,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0) ),
    inference(resolution,[],[f95,f66])).

fof(f95,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK2(k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK1(k1_tarski(sK0),X2),X2)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK1(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f117,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f116,f65])).

fof(f116,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f115,f35])).

fof(f115,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f141,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f140,f65])).

fof(f140,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f139,f35])).

fof(f139,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f129,f39])).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f229,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,sK0)
      | X0 = X3 ) ),
    inference(backward_demodulation,[],[f66,f224])).

fof(f335,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f152,f314])).

fof(f152,plain,(
    k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f143,f58])).

fof(f58,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f143,plain,(
    sK0 != k1_setfam_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (4501)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (4509)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.55  % (4517)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.56  % (4496)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.52/0.57  % (4510)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.52/0.57  % (4494)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.57  % (4516)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.57  % (4494)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f355,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(subsumption_resolution,[],[f335,f314])).
% 1.52/0.57  fof(f314,plain,(
% 1.52/0.57    ( ! [X0,X3] : (X0 = X3) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f229,f228])).
% 1.52/0.57  fof(f228,plain,(
% 1.52/0.57    ( ! [X3] : (r2_hidden(X3,sK0)) )),
% 1.52/0.57    inference(backward_demodulation,[],[f65,f224])).
% 1.52/0.57  fof(f224,plain,(
% 1.52/0.57    ( ! [X6] : (sK0 = X6) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f220,f68])).
% 1.52/0.57  fof(f68,plain,(
% 1.52/0.57    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.52/0.57    inference(equality_resolution,[],[f49])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.52/0.57    inference(flattening,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f7])).
% 1.52/0.58  fof(f7,axiom,(
% 1.52/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.52/0.58  fof(f220,plain,(
% 1.52/0.58    ( ! [X6] : (~r1_tarski(k1_xboole_0,k1_tarski(X6)) | sK0 = X6) )),
% 1.52/0.58    inference(resolution,[],[f169,f66])).
% 1.52/0.58  fof(f66,plain,(
% 1.52/0.58    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.52/0.58    inference(equality_resolution,[],[f44])).
% 1.52/0.58  fof(f44,plain,(
% 1.52/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.52/0.58    inference(cnf_transformation,[],[f26])).
% 1.52/0.58  fof(f26,plain,(
% 1.52/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.52/0.58  fof(f25,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f24,plain,(
% 1.52/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.52/0.58    inference(rectify,[],[f23])).
% 1.52/0.58  fof(f23,plain,(
% 1.52/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.52/0.58    inference(nnf_transformation,[],[f3])).
% 1.52/0.58  fof(f3,axiom,(
% 1.52/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.52/0.58  fof(f169,plain,(
% 1.52/0.58    ( ! [X0] : (r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.52/0.58    inference(resolution,[],[f161,f51])).
% 1.52/0.58  fof(f51,plain,(
% 1.52/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f32])).
% 1.52/0.58  fof(f32,plain,(
% 1.52/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.52/0.58  fof(f31,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f30,plain,(
% 1.52/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.58    inference(rectify,[],[f29])).
% 1.52/0.58  fof(f29,plain,(
% 1.52/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.58    inference(nnf_transformation,[],[f14])).
% 1.52/0.58  fof(f14,plain,(
% 1.52/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.58    inference(ennf_transformation,[],[f1])).
% 1.52/0.58  fof(f1,axiom,(
% 1.52/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.58  fof(f161,plain,(
% 1.52/0.58    r2_hidden(sK0,k1_xboole_0)),
% 1.52/0.58    inference(superposition,[],[f65,f142])).
% 1.52/0.58  fof(f142,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f141,f129])).
% 1.52/0.58  fof(f129,plain,(
% 1.52/0.58    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f125,f35])).
% 1.52/0.58  fof(f35,plain,(
% 1.52/0.58    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.52/0.58    inference(cnf_transformation,[],[f16])).
% 1.52/0.58  fof(f16,plain,(
% 1.52/0.58    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).
% 1.52/0.58  fof(f15,plain,(
% 1.52/0.58    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f12,plain,(
% 1.52/0.58    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.52/0.58    inference(ennf_transformation,[],[f11])).
% 1.52/0.58  fof(f11,negated_conjecture,(
% 1.52/0.58    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.52/0.58    inference(negated_conjecture,[],[f10])).
% 1.52/0.58  fof(f10,conjecture,(
% 1.52/0.58    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.52/0.58  fof(f125,plain,(
% 1.52/0.58    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(duplicate_literal_removal,[],[f124])).
% 1.52/0.58  fof(f124,plain,(
% 1.52/0.58    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(superposition,[],[f41,f118])).
% 1.52/0.58  fof(f118,plain,(
% 1.52/0.58    sK0 = sK2(k1_tarski(sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f117,f96])).
% 1.52/0.58  fof(f96,plain,(
% 1.52/0.58    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0)),
% 1.52/0.58    inference(resolution,[],[f95,f66])).
% 1.52/0.58  fof(f95,plain,(
% 1.52/0.58    r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(equality_resolution,[],[f75])).
% 1.52/0.58  fof(f75,plain,(
% 1.52/0.58    ( ! [X2] : (sK0 != X2 | r2_hidden(sK2(k1_tarski(sK0),X2),k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),X2),X2) | k1_xboole_0 = k1_tarski(sK0)) )),
% 1.52/0.58    inference(superposition,[],[f35,f40])).
% 1.52/0.58  fof(f40,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 1.52/0.58    inference(cnf_transformation,[],[f22])).
% 1.52/0.58  fof(f22,plain,(
% 1.52/0.58    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 1.52/0.58  fof(f19,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f20,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f21,plain,(
% 1.52/0.58    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f18,plain,(
% 1.52/0.58    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 1.52/0.58    inference(rectify,[],[f17])).
% 1.52/0.58  fof(f17,plain,(
% 1.52/0.58    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 1.52/0.58    inference(nnf_transformation,[],[f13])).
% 1.52/0.58  fof(f13,plain,(
% 1.52/0.58    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.52/0.58    inference(ennf_transformation,[],[f9])).
% 1.52/0.58  fof(f9,axiom,(
% 1.52/0.58    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.52/0.58  fof(f117,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f116,f65])).
% 1.52/0.58  fof(f116,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f115,f35])).
% 1.52/0.58  fof(f115,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 1.52/0.58    inference(duplicate_literal_removal,[],[f106])).
% 1.52/0.58  fof(f106,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(resolution,[],[f96,f39])).
% 1.52/0.58  fof(f39,plain,(
% 1.52/0.58    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 1.52/0.58    inference(cnf_transformation,[],[f22])).
% 1.52/0.58  fof(f41,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 1.52/0.58    inference(cnf_transformation,[],[f22])).
% 1.52/0.58  fof(f141,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f140,f65])).
% 1.52/0.58  fof(f140,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 1.52/0.58    inference(subsumption_resolution,[],[f139,f35])).
% 1.52/0.58  fof(f139,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 1.52/0.58    inference(duplicate_literal_removal,[],[f130])).
% 1.52/0.58  fof(f130,plain,(
% 1.52/0.58    k1_xboole_0 = k1_tarski(sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.52/0.58    inference(resolution,[],[f129,f39])).
% 1.52/0.58  fof(f65,plain,(
% 1.52/0.58    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.52/0.58    inference(equality_resolution,[],[f64])).
% 1.52/0.58  fof(f64,plain,(
% 1.52/0.58    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.52/0.58    inference(equality_resolution,[],[f45])).
% 1.52/0.58  fof(f45,plain,(
% 1.52/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.52/0.58    inference(cnf_transformation,[],[f26])).
% 1.52/0.58  fof(f229,plain,(
% 1.52/0.58    ( ! [X0,X3] : (~r2_hidden(X3,sK0) | X0 = X3) )),
% 1.52/0.58    inference(backward_demodulation,[],[f66,f224])).
% 1.52/0.58  fof(f335,plain,(
% 1.52/0.58    ( ! [X0] : (k1_xboole_0 != X0) )),
% 1.52/0.58    inference(superposition,[],[f152,f314])).
% 1.52/0.58  fof(f152,plain,(
% 1.52/0.58    k1_xboole_0 != sK0),
% 1.52/0.58    inference(forward_demodulation,[],[f143,f58])).
% 1.52/0.58  fof(f58,plain,(
% 1.52/0.58    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 1.52/0.58    inference(equality_resolution,[],[f57])).
% 1.52/0.58  fof(f57,plain,(
% 1.52/0.58    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 1.52/0.58    inference(equality_resolution,[],[f43])).
% 1.52/0.58  fof(f43,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | k1_xboole_0 != X1 | k1_xboole_0 != X0) )),
% 1.52/0.58    inference(cnf_transformation,[],[f22])).
% 1.52/0.58  fof(f143,plain,(
% 1.52/0.58    sK0 != k1_setfam_1(k1_xboole_0)),
% 1.52/0.58    inference(backward_demodulation,[],[f35,f142])).
% 1.52/0.58  % SZS output end Proof for theBenchmark
% 1.52/0.58  % (4494)------------------------------
% 1.52/0.58  % (4494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (4494)Termination reason: Refutation
% 1.52/0.58  
% 1.52/0.58  % (4494)Memory used [KB]: 1791
% 1.52/0.58  % (4494)Time elapsed: 0.165 s
% 1.52/0.58  % (4494)------------------------------
% 1.52/0.58  % (4494)------------------------------
% 1.52/0.58  % (4508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.58  % (4518)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.58  % (4502)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.59  % (4493)Success in time 0.23 s
%------------------------------------------------------------------------------
