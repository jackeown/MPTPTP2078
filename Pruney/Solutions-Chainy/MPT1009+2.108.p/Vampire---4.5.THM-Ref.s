%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:41 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 257 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   25
%              Number of atoms          :  530 ( 988 expanded)
%              Number of equality atoms :  283 ( 382 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f955,plain,(
    $false ),
    inference(subsumption_resolution,[],[f954,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f954,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK1))) ),
    inference(forward_demodulation,[],[f914,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f914,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK3),k1_tarski(k1_funct_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f217,f906])).

fof(f906,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f885,f68])).

fof(f885,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(backward_demodulation,[],[f446,f873])).

fof(f873,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f868,f287])).

fof(f287,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f285,f70])).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f285,plain,(
    ! [X0,X1] : r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f284,f74])).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f284,plain,(
    ! [X2,X0,X1] : r2_hidden(X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f283,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f283,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f282,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f282,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f281,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f281,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f279,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f279,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r2_hidden(X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f243,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f243,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) ),
    inference(resolution,[],[f134,f126])).

fof(f126,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] :
      ( ~ sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8)
      | r2_hidden(X10,X8) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X0 != X10
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).

fof(f61,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X0 != X9
              & X1 != X9
              & X2 != X9
              & X3 != X9
              & X4 != X9
              & X5 != X9
              & X6 != X9
              & X7 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X0 = X9
            | X1 = X9
            | X2 = X9
            | X3 = X9
            | X4 = X9
            | X5 = X9
            | X6 = X9
            | X7 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9
                & X7 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | X7 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f134,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) )
      & ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ),
    inference(definition_folding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(f868,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(resolution,[],[f686,f156])).

fof(f156,plain,(
    v4_relat_1(sK4,k1_tarski(sK1)) ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f686,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK4,k1_tarski(X1))
      | k1_xboole_0 = k1_relat_1(sK4)
      | ~ r2_hidden(sK1,k1_tarski(X1)) ) ),
    inference(subsumption_resolution,[],[f684,f141])).

fof(f141,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f139,f73])).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(resolution,[],[f72,f65])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f684,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k1_tarski(X1))
      | k1_xboole_0 = k1_relat_1(sK4)
      | ~ v4_relat_1(sK4,k1_tarski(X1))
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f678,f174])).

fof(f174,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k1_tarski(X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v4_relat_1(X2,k1_tarski(X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f84,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f678,plain,(
    ~ r2_hidden(sK1,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f676,f141])).

fof(f676,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f620,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f620,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK1,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f619,f156])).

fof(f619,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK1,k1_relat_1(sK4))
    | ~ v4_relat_1(sK4,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f609,f141])).

fof(f609,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v4_relat_1(sK4,k1_tarski(sK1)) ),
    inference(superposition,[],[f223,f263])).

fof(f263,plain,(
    ! [X2,X1] :
      ( k2_relat_1(X1) = k11_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,k1_tarski(X2)) ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X2,X1] :
      ( k2_relat_1(X1) = k11_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,k1_tarski(X2))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f170,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f170,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f76,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f223,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1))
    | ~ r2_hidden(sK1,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f222,f141])).

fof(f222,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1))
    | ~ r2_hidden(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f218,f64])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f218,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1))
    | ~ r2_hidden(sK1,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f217,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f446,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f445,f68])).

fof(f445,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 = sK4
    | ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0) ),
    inference(superposition,[],[f440,f125])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f440,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,sK2),sK4)
      | sK4 = k2_zfmisc_1(X1,sK2)
      | ~ r1_tarski(k1_relat_1(sK4),X1) ) ),
    inference(resolution,[],[f420,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f420,plain,(
    ! [X0] :
      ( r1_tarski(sK4,k2_zfmisc_1(X0,sK2))
      | ~ r1_tarski(k1_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f228,f65])).

fof(f228,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ r1_tarski(k1_relat_1(X8),X9)
      | r1_tarski(X8,k2_zfmisc_1(X9,X11)) ) ),
    inference(resolution,[],[f96,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f217,plain,(
    ~ r1_tarski(k9_relat_1(sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(subsumption_resolution,[],[f216,f65])).

fof(f216,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(superposition,[],[f67,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f67,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (26466)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (26489)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (26474)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (26474)Refutation not found, incomplete strategy% (26474)------------------------------
% 0.20/0.50  % (26474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26472)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (26474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26474)Memory used [KB]: 10874
% 0.20/0.51  % (26474)Time elapsed: 0.099 s
% 0.20/0.51  % (26474)------------------------------
% 0.20/0.51  % (26474)------------------------------
% 0.20/0.51  % (26484)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (26488)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (26468)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (26477)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (26488)Refutation not found, incomplete strategy% (26488)------------------------------
% 0.20/0.52  % (26488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26488)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26488)Memory used [KB]: 10746
% 0.20/0.52  % (26488)Time elapsed: 0.092 s
% 0.20/0.52  % (26488)------------------------------
% 0.20/0.52  % (26488)------------------------------
% 0.20/0.52  % (26470)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (26469)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (26465)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (26465)Refutation not found, incomplete strategy% (26465)------------------------------
% 0.20/0.52  % (26465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26465)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26465)Memory used [KB]: 1791
% 0.20/0.52  % (26465)Time elapsed: 0.115 s
% 0.20/0.52  % (26465)------------------------------
% 0.20/0.52  % (26465)------------------------------
% 0.20/0.52  % (26467)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (26471)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (26464)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26473)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (26491)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (26479)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (26491)Refutation not found, incomplete strategy% (26491)------------------------------
% 0.20/0.53  % (26491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26491)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26491)Memory used [KB]: 6268
% 0.20/0.53  % (26491)Time elapsed: 0.135 s
% 0.20/0.53  % (26491)------------------------------
% 0.20/0.53  % (26491)------------------------------
% 0.20/0.53  % (26492)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (26486)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (26493)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (26480)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (26483)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (26487)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (26480)Refutation not found, incomplete strategy% (26480)------------------------------
% 0.20/0.53  % (26480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26480)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26480)Memory used [KB]: 10746
% 0.20/0.53  % (26480)Time elapsed: 0.140 s
% 0.20/0.53  % (26480)------------------------------
% 0.20/0.53  % (26480)------------------------------
% 0.20/0.53  % (26475)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (26485)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (26478)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (26482)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (26481)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (26493)Refutation not found, incomplete strategy% (26493)------------------------------
% 0.20/0.55  % (26493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26493)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26493)Memory used [KB]: 1791
% 0.20/0.55  % (26493)Time elapsed: 0.152 s
% 0.20/0.55  % (26493)------------------------------
% 0.20/0.55  % (26493)------------------------------
% 0.20/0.55  % (26492)Refutation not found, incomplete strategy% (26492)------------------------------
% 0.20/0.55  % (26492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26492)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26492)Memory used [KB]: 10874
% 0.20/0.55  % (26492)Time elapsed: 0.163 s
% 0.20/0.55  % (26492)------------------------------
% 0.20/0.55  % (26492)------------------------------
% 0.20/0.57  % (26476)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.57  % (26490)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.72/0.58  % (26473)Refutation found. Thanks to Tanya!
% 1.72/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.58  % SZS output start Proof for theBenchmark
% 1.72/0.58  fof(f955,plain,(
% 1.72/0.58    $false),
% 1.72/0.58    inference(subsumption_resolution,[],[f954,f68])).
% 1.72/0.58  fof(f68,plain,(
% 1.72/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f2])).
% 1.72/0.58  fof(f2,axiom,(
% 1.72/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.72/0.58  fof(f954,plain,(
% 1.72/0.58    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK1)))),
% 1.72/0.58    inference(forward_demodulation,[],[f914,f69])).
% 1.72/0.58  fof(f69,plain,(
% 1.72/0.58    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f20])).
% 1.72/0.58  fof(f20,axiom,(
% 1.72/0.58    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 1.72/0.58  fof(f914,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(k1_xboole_0,sK3),k1_tarski(k1_funct_1(k1_xboole_0,sK1)))),
% 1.72/0.58    inference(backward_demodulation,[],[f217,f906])).
% 1.72/0.58  fof(f906,plain,(
% 1.72/0.58    k1_xboole_0 = sK4),
% 1.72/0.58    inference(subsumption_resolution,[],[f885,f68])).
% 1.72/0.58  fof(f885,plain,(
% 1.72/0.58    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK4),
% 1.72/0.58    inference(backward_demodulation,[],[f446,f873])).
% 1.72/0.58  fof(f873,plain,(
% 1.72/0.58    k1_xboole_0 = k1_relat_1(sK4)),
% 1.72/0.58    inference(subsumption_resolution,[],[f868,f287])).
% 1.72/0.58  fof(f287,plain,(
% 1.72/0.58    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.72/0.58    inference(superposition,[],[f285,f70])).
% 1.72/0.58  fof(f70,plain,(
% 1.72/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f3])).
% 1.72/0.58  fof(f3,axiom,(
% 1.72/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.72/0.58  fof(f285,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(X1,k2_tarski(X0,X1))) )),
% 1.72/0.58    inference(superposition,[],[f284,f74])).
% 1.72/0.58  fof(f74,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f4])).
% 1.72/0.58  fof(f4,axiom,(
% 1.72/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.72/0.58  fof(f284,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_enumset1(X0,X1,X2))) )),
% 1.72/0.58    inference(superposition,[],[f283,f92])).
% 1.72/0.58  fof(f92,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f5])).
% 1.72/0.58  fof(f5,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.72/0.58  fof(f283,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_enumset1(X0,X1,X2,X3))) )),
% 1.72/0.58    inference(superposition,[],[f282,f94])).
% 1.72/0.58  fof(f94,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f6])).
% 1.72/0.58  fof(f6,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.72/0.58  fof(f282,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.72/0.58    inference(superposition,[],[f281,f97])).
% 1.72/0.58  fof(f97,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f7])).
% 1.72/0.58  fof(f7,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.72/0.58  fof(f281,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.72/0.58    inference(superposition,[],[f279,f98])).
% 1.72/0.58  fof(f98,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f8])).
% 1.72/0.58  fof(f8,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.72/0.58  fof(f279,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_hidden(X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.72/0.58    inference(superposition,[],[f243,f99])).
% 1.72/0.58  fof(f99,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f9])).
% 1.72/0.58  fof(f9,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.72/0.58  fof(f243,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0))) )),
% 1.72/0.58    inference(resolution,[],[f134,f126])).
% 1.72/0.58  fof(f126,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : (~sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8) | r2_hidden(X10,X8)) )),
% 1.72/0.58    inference(equality_resolution,[],[f108])).
% 1.72/0.58  fof(f108,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X0 != X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f62])).
% 1.72/0.58  fof(f62,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (((sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).
% 1.72/0.58  fof(f61,plain,(
% 1.72/0.58    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8))) => (((sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f60,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.72/0.58    inference(rectify,[],[f59])).
% 1.72/0.58  fof(f59,plain,(
% 1.72/0.58    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 1.72/0.58    inference(flattening,[],[f58])).
% 1.72/0.58  fof(f58,plain,(
% 1.72/0.58    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 1.72/0.58    inference(nnf_transformation,[],[f46])).
% 1.72/0.58  fof(f46,plain,(
% 1.72/0.58    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.72/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.72/0.58  fof(f134,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.72/0.58    inference(equality_resolution,[],[f118])).
% 1.72/0.58  fof(f118,plain,(
% 1.72/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.72/0.58    inference(cnf_transformation,[],[f63])).
% 1.72/0.58  fof(f63,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)) & (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.72/0.58    inference(nnf_transformation,[],[f47])).
% 1.72/0.58  fof(f47,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8))),
% 1.72/0.58    inference(definition_folding,[],[f45,f46])).
% 1.72/0.58  fof(f45,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.72/0.58    inference(ennf_transformation,[],[f12])).
% 1.72/0.58  fof(f12,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 1.72/0.58  fof(f868,plain,(
% 1.72/0.58    k1_xboole_0 = k1_relat_1(sK4) | ~r2_hidden(sK1,k1_tarski(sK1))),
% 1.72/0.58    inference(resolution,[],[f686,f156])).
% 1.72/0.58  fof(f156,plain,(
% 1.72/0.58    v4_relat_1(sK4,k1_tarski(sK1))),
% 1.72/0.58    inference(resolution,[],[f93,f65])).
% 1.72/0.58  fof(f65,plain,(
% 1.72/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.72/0.58    inference(cnf_transformation,[],[f49])).
% 1.72/0.58  fof(f49,plain,(
% 1.72/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4)),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f48])).
% 1.72/0.58  fof(f48,plain,(
% 1.72/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f31,plain,(
% 1.72/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.72/0.58    inference(flattening,[],[f30])).
% 1.72/0.58  fof(f30,plain,(
% 1.72/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.72/0.58    inference(ennf_transformation,[],[f28])).
% 1.72/0.58  fof(f28,plain,(
% 1.72/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.72/0.58    inference(pure_predicate_removal,[],[f27])).
% 1.72/0.58  fof(f27,negated_conjecture,(
% 1.72/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.72/0.58    inference(negated_conjecture,[],[f26])).
% 1.72/0.58  fof(f26,conjecture,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.72/0.58  fof(f93,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f41])).
% 1.72/0.58  fof(f41,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(ennf_transformation,[],[f29])).
% 1.72/0.58  fof(f29,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.72/0.58    inference(pure_predicate_removal,[],[f23])).
% 1.72/0.58  fof(f23,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.72/0.58  fof(f686,plain,(
% 1.72/0.58    ( ! [X1] : (~v4_relat_1(sK4,k1_tarski(X1)) | k1_xboole_0 = k1_relat_1(sK4) | ~r2_hidden(sK1,k1_tarski(X1))) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f684,f141])).
% 1.72/0.58  fof(f141,plain,(
% 1.72/0.58    v1_relat_1(sK4)),
% 1.72/0.58    inference(subsumption_resolution,[],[f139,f73])).
% 1.72/0.58  fof(f73,plain,(
% 1.72/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f17])).
% 1.72/0.58  fof(f17,axiom,(
% 1.72/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.72/0.58  fof(f139,plain,(
% 1.72/0.58    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.72/0.58    inference(resolution,[],[f72,f65])).
% 1.72/0.58  fof(f72,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f33])).
% 1.72/0.58  fof(f33,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f14])).
% 1.72/0.58  fof(f14,axiom,(
% 1.72/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.72/0.58  fof(f684,plain,(
% 1.72/0.58    ( ! [X1] : (~r2_hidden(sK1,k1_tarski(X1)) | k1_xboole_0 = k1_relat_1(sK4) | ~v4_relat_1(sK4,k1_tarski(X1)) | ~v1_relat_1(sK4)) )),
% 1.72/0.58    inference(superposition,[],[f678,f174])).
% 1.72/0.58  fof(f174,plain,(
% 1.72/0.58    ( ! [X2,X3] : (k1_relat_1(X2) = k1_tarski(X3) | k1_xboole_0 = k1_relat_1(X2) | ~v4_relat_1(X2,k1_tarski(X3)) | ~v1_relat_1(X2)) )),
% 1.72/0.58    inference(resolution,[],[f84,f77])).
% 1.72/0.58  fof(f77,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f50])).
% 1.72/0.58  fof(f50,plain,(
% 1.72/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(nnf_transformation,[],[f36])).
% 1.72/0.58  fof(f36,plain,(
% 1.72/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f16])).
% 1.72/0.58  fof(f16,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.72/0.58  fof(f84,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f54])).
% 1.72/0.58  fof(f54,plain,(
% 1.72/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.72/0.58    inference(flattening,[],[f53])).
% 1.72/0.58  fof(f53,plain,(
% 1.72/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.72/0.58    inference(nnf_transformation,[],[f10])).
% 1.72/0.58  fof(f10,axiom,(
% 1.72/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.72/0.58  fof(f678,plain,(
% 1.72/0.58    ~r2_hidden(sK1,k1_relat_1(sK4))),
% 1.72/0.58    inference(subsumption_resolution,[],[f676,f141])).
% 1.72/0.58  fof(f676,plain,(
% 1.72/0.58    ~r2_hidden(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.72/0.58    inference(resolution,[],[f620,f75])).
% 1.72/0.58  fof(f75,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f34])).
% 1.72/0.58  fof(f34,plain,(
% 1.72/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f18])).
% 1.72/0.58  fof(f18,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.72/0.58  fof(f620,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~r2_hidden(sK1,k1_relat_1(sK4))),
% 1.72/0.58    inference(subsumption_resolution,[],[f619,f156])).
% 1.72/0.58  fof(f619,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~r2_hidden(sK1,k1_relat_1(sK4)) | ~v4_relat_1(sK4,k1_tarski(sK1))),
% 1.72/0.58    inference(subsumption_resolution,[],[f609,f141])).
% 1.72/0.58  fof(f609,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~r2_hidden(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v4_relat_1(sK4,k1_tarski(sK1))),
% 1.72/0.58    inference(superposition,[],[f223,f263])).
% 1.72/0.58  fof(f263,plain,(
% 1.72/0.58    ( ! [X2,X1] : (k2_relat_1(X1) = k11_relat_1(X1,X2) | ~v1_relat_1(X1) | ~v4_relat_1(X1,k1_tarski(X2))) )),
% 1.72/0.58    inference(duplicate_literal_removal,[],[f253])).
% 1.72/0.58  fof(f253,plain,(
% 1.72/0.58    ( ! [X2,X1] : (k2_relat_1(X1) = k11_relat_1(X1,X2) | ~v1_relat_1(X1) | ~v4_relat_1(X1,k1_tarski(X2)) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(superposition,[],[f170,f71])).
% 1.72/0.58  fof(f71,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f32])).
% 1.72/0.58  fof(f32,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f15])).
% 1.72/0.58  fof(f15,axiom,(
% 1.72/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.72/0.58  fof(f170,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.72/0.58    inference(duplicate_literal_removal,[],[f169])).
% 1.72/0.58  fof(f169,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.72/0.58    inference(superposition,[],[f76,f80])).
% 1.72/0.58  fof(f80,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f40])).
% 1.72/0.58  fof(f40,plain,(
% 1.72/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(flattening,[],[f39])).
% 1.72/0.58  fof(f39,plain,(
% 1.72/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.72/0.58    inference(ennf_transformation,[],[f21])).
% 1.72/0.58  fof(f21,axiom,(
% 1.72/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.72/0.58  fof(f76,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f35])).
% 1.72/0.58  fof(f35,plain,(
% 1.72/0.58    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f19])).
% 1.72/0.58  fof(f19,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.72/0.58  fof(f223,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) | ~r2_hidden(sK1,k1_relat_1(sK4))),
% 1.72/0.58    inference(subsumption_resolution,[],[f222,f141])).
% 1.72/0.58  fof(f222,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) | ~r2_hidden(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.72/0.58    inference(subsumption_resolution,[],[f218,f64])).
% 1.72/0.58  fof(f64,plain,(
% 1.72/0.58    v1_funct_1(sK4)),
% 1.72/0.58    inference(cnf_transformation,[],[f49])).
% 1.72/0.58  fof(f218,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) | ~r2_hidden(sK1,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.72/0.58    inference(superposition,[],[f217,f79])).
% 1.72/0.58  fof(f79,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f38])).
% 1.72/0.58  fof(f38,plain,(
% 1.72/0.58    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(flattening,[],[f37])).
% 1.72/0.58  fof(f37,plain,(
% 1.72/0.58    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.72/0.58    inference(ennf_transformation,[],[f22])).
% 1.72/0.58  fof(f22,axiom,(
% 1.72/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.72/0.58  fof(f446,plain,(
% 1.72/0.58    ~r1_tarski(k1_relat_1(sK4),k1_xboole_0) | k1_xboole_0 = sK4),
% 1.72/0.58    inference(subsumption_resolution,[],[f445,f68])).
% 1.72/0.58  fof(f445,plain,(
% 1.72/0.58    ~r1_tarski(k1_xboole_0,sK4) | k1_xboole_0 = sK4 | ~r1_tarski(k1_relat_1(sK4),k1_xboole_0)),
% 1.72/0.58    inference(superposition,[],[f440,f125])).
% 1.72/0.58  fof(f125,plain,(
% 1.72/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.72/0.58    inference(equality_resolution,[],[f90])).
% 1.72/0.58  fof(f90,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f57])).
% 1.72/0.58  fof(f57,plain,(
% 1.72/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.72/0.58    inference(flattening,[],[f56])).
% 1.72/0.58  fof(f56,plain,(
% 1.72/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.72/0.58    inference(nnf_transformation,[],[f11])).
% 1.72/0.58  fof(f11,axiom,(
% 1.72/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.72/0.58  fof(f440,plain,(
% 1.72/0.58    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(X1,sK2),sK4) | sK4 = k2_zfmisc_1(X1,sK2) | ~r1_tarski(k1_relat_1(sK4),X1)) )),
% 1.72/0.58    inference(resolution,[],[f420,f83])).
% 1.72/0.58  fof(f83,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f52])).
% 1.72/0.58  fof(f52,plain,(
% 1.72/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.58    inference(flattening,[],[f51])).
% 1.72/0.58  fof(f51,plain,(
% 1.72/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.58    inference(nnf_transformation,[],[f1])).
% 1.72/0.58  fof(f1,axiom,(
% 1.72/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.72/0.58  fof(f420,plain,(
% 1.72/0.58    ( ! [X0] : (r1_tarski(sK4,k2_zfmisc_1(X0,sK2)) | ~r1_tarski(k1_relat_1(sK4),X0)) )),
% 1.72/0.58    inference(resolution,[],[f228,f65])).
% 1.72/0.58  fof(f228,plain,(
% 1.72/0.58    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~r1_tarski(k1_relat_1(X8),X9) | r1_tarski(X8,k2_zfmisc_1(X9,X11))) )),
% 1.72/0.58    inference(resolution,[],[f96,f87])).
% 1.72/0.58  fof(f87,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f55])).
% 1.72/0.58  fof(f55,plain,(
% 1.72/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.72/0.58    inference(nnf_transformation,[],[f13])).
% 1.72/0.58  fof(f13,axiom,(
% 1.72/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.72/0.58  fof(f96,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f44])).
% 1.72/0.58  fof(f44,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.72/0.58    inference(flattening,[],[f43])).
% 1.72/0.58  fof(f43,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.72/0.58    inference(ennf_transformation,[],[f25])).
% 1.72/0.58  fof(f25,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 1.72/0.58  fof(f217,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 1.72/0.58    inference(subsumption_resolution,[],[f216,f65])).
% 1.72/0.58  fof(f216,plain,(
% 1.72/0.58    ~r1_tarski(k9_relat_1(sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.72/0.58    inference(superposition,[],[f67,f95])).
% 1.72/0.58  fof(f95,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f42])).
% 1.72/0.58  fof(f42,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(ennf_transformation,[],[f24])).
% 1.72/0.58  fof(f24,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.72/0.58  fof(f67,plain,(
% 1.72/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 1.72/0.58    inference(cnf_transformation,[],[f49])).
% 1.72/0.58  % SZS output end Proof for theBenchmark
% 1.72/0.58  % (26473)------------------------------
% 1.72/0.58  % (26473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (26473)Termination reason: Refutation
% 1.72/0.58  
% 1.72/0.58  % (26473)Memory used [KB]: 2174
% 1.72/0.58  % (26473)Time elapsed: 0.176 s
% 1.72/0.58  % (26473)------------------------------
% 1.72/0.58  % (26473)------------------------------
% 1.72/0.58  % (26463)Success in time 0.227 s
%------------------------------------------------------------------------------
