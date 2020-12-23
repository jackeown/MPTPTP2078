%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 342 expanded)
%              Number of leaves         :    8 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  177 (2183 expanded)
%              Number of equality atoms :   33 ( 364 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1140,plain,(
    $false ),
    inference(resolution,[],[f1137,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1137,plain,(
    ! [X6] : ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f712,f1132])).

fof(f1132,plain,(
    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f1129,f698])).

fof(f698,plain,(
    ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(global_subsumption,[],[f567,f682])).

fof(f682,plain,(
    ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f674,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f674,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f212,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f212,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f142,f69])).

fof(f142,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f134,f96])).

fof(f96,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f38,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f38,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f134,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f98,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f38,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f567,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f561])).

fof(f561,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f187,f47])).

fof(f187,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f106,f68])).

fof(f106,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f38,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1129,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) ),
    inference(resolution,[],[f729,f44])).

fof(f729,plain,(
    ! [X7] :
      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X7)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) ) ),
    inference(subsumption_resolution,[],[f389,f698])).

fof(f389,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7)
      | ~ r1_tarski(k3_xboole_0(sK0,sK1),X7) ) ),
    inference(superposition,[],[f122,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f39])).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f122,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f96,f68])).

fof(f712,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
      | ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f240,f698])).

fof(f240,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f121,f66])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f96,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17497)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (17497)Refutation not found, incomplete strategy% (17497)------------------------------
% 0.22/0.51  % (17497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17505)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (17497)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17497)Memory used [KB]: 10618
% 0.22/0.52  % (17497)Time elapsed: 0.103 s
% 0.22/0.52  % (17497)------------------------------
% 0.22/0.52  % (17497)------------------------------
% 0.22/0.52  % (17489)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (17489)Refutation not found, incomplete strategy% (17489)------------------------------
% 0.22/0.52  % (17489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17489)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17489)Memory used [KB]: 10618
% 0.22/0.52  % (17489)Time elapsed: 0.111 s
% 0.22/0.52  % (17489)------------------------------
% 0.22/0.52  % (17489)------------------------------
% 0.22/0.52  % (17488)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.53  % (17494)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.53  % (17505)Refutation not found, incomplete strategy% (17505)------------------------------
% 1.33/0.53  % (17505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (17505)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (17505)Memory used [KB]: 6140
% 1.33/0.53  % (17505)Time elapsed: 0.112 s
% 1.33/0.53  % (17505)------------------------------
% 1.33/0.53  % (17505)------------------------------
% 1.33/0.53  % (17483)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.53  % (17482)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (17485)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.54  % (17484)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.54  % (17484)Refutation not found, incomplete strategy% (17484)------------------------------
% 1.33/0.54  % (17484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (17484)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (17484)Memory used [KB]: 6140
% 1.33/0.54  % (17484)Time elapsed: 0.124 s
% 1.33/0.54  % (17484)------------------------------
% 1.33/0.54  % (17484)------------------------------
% 1.33/0.54  % (17481)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (17498)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.54  % (17480)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.54  % (17480)Refutation not found, incomplete strategy% (17480)------------------------------
% 1.33/0.54  % (17480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (17480)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (17480)Memory used [KB]: 1663
% 1.33/0.54  % (17480)Time elapsed: 0.133 s
% 1.33/0.54  % (17480)------------------------------
% 1.33/0.54  % (17480)------------------------------
% 1.33/0.54  % (17488)Refutation not found, incomplete strategy% (17488)------------------------------
% 1.33/0.54  % (17488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (17488)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (17488)Memory used [KB]: 10618
% 1.33/0.54  % (17488)Time elapsed: 0.132 s
% 1.33/0.54  % (17488)------------------------------
% 1.33/0.54  % (17488)------------------------------
% 1.33/0.54  % (17508)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (17496)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.54  % (17490)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.55  % (17502)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.55  % (17503)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.55  % (17509)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.55  % (17490)Refutation not found, incomplete strategy% (17490)------------------------------
% 1.48/0.55  % (17490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (17490)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (17490)Memory used [KB]: 10618
% 1.48/0.55  % (17490)Time elapsed: 0.133 s
% 1.48/0.55  % (17490)------------------------------
% 1.48/0.55  % (17490)------------------------------
% 1.48/0.55  % (17487)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.55  % (17502)Refutation not found, incomplete strategy% (17502)------------------------------
% 1.48/0.55  % (17502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (17502)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (17502)Memory used [KB]: 10746
% 1.48/0.55  % (17502)Time elapsed: 0.099 s
% 1.48/0.55  % (17502)------------------------------
% 1.48/0.55  % (17502)------------------------------
% 1.48/0.55  % (17500)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.55  % (17491)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.55  % (17482)Refutation not found, incomplete strategy% (17482)------------------------------
% 1.48/0.55  % (17482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (17482)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (17482)Memory used [KB]: 10618
% 1.48/0.55  % (17482)Time elapsed: 0.128 s
% 1.48/0.55  % (17482)------------------------------
% 1.48/0.55  % (17482)------------------------------
% 1.48/0.55  % (17500)Refutation not found, incomplete strategy% (17500)------------------------------
% 1.48/0.55  % (17500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (17500)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (17500)Memory used [KB]: 10746
% 1.48/0.55  % (17500)Time elapsed: 0.147 s
% 1.48/0.55  % (17500)------------------------------
% 1.48/0.55  % (17500)------------------------------
% 1.48/0.55  % (17506)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (17492)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.55  % (17499)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.55  % (17501)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.55  % (17501)Refutation not found, incomplete strategy% (17501)------------------------------
% 1.48/0.55  % (17501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (17501)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (17501)Memory used [KB]: 1663
% 1.48/0.55  % (17501)Time elapsed: 0.147 s
% 1.48/0.55  % (17501)------------------------------
% 1.48/0.55  % (17501)------------------------------
% 1.48/0.56  % (17486)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.56  % (17493)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (17495)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.56  % (17495)Refutation not found, incomplete strategy% (17495)------------------------------
% 1.48/0.56  % (17495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (17495)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (17495)Memory used [KB]: 6140
% 1.48/0.56  % (17495)Time elapsed: 0.001 s
% 1.48/0.56  % (17495)------------------------------
% 1.48/0.56  % (17495)------------------------------
% 1.48/0.56  % (17504)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.57  % (17507)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.92/0.63  % (17511)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.92/0.63  % (17511)Refutation not found, incomplete strategy% (17511)------------------------------
% 1.92/0.63  % (17511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.63  % (17511)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.63  
% 1.92/0.63  % (17511)Memory used [KB]: 6140
% 1.92/0.63  % (17511)Time elapsed: 0.005 s
% 1.92/0.63  % (17511)------------------------------
% 1.92/0.63  % (17511)------------------------------
% 1.92/0.64  % (17512)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.92/0.66  % (17513)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.92/0.67  % (17515)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.92/0.67  % (17517)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 1.92/0.67  % (17514)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.18/0.68  % (17518)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.18/0.68  % (17516)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.18/0.69  % (17519)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.18/0.69  % (17519)Refutation not found, incomplete strategy% (17519)------------------------------
% 2.18/0.69  % (17519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (17519)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (17519)Memory used [KB]: 1663
% 2.18/0.69  % (17519)Time elapsed: 0.111 s
% 2.18/0.69  % (17519)------------------------------
% 2.18/0.69  % (17519)------------------------------
% 2.18/0.69  % (17520)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.18/0.69  % (17521)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.18/0.70  % (17522)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.53/0.76  % (17523)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.59/0.81  % (17485)Time limit reached!
% 2.59/0.81  % (17485)------------------------------
% 2.59/0.81  % (17485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.81  % (17485)Termination reason: Time limit
% 2.59/0.81  
% 2.59/0.81  % (17485)Memory used [KB]: 9466
% 2.59/0.81  % (17485)Time elapsed: 0.404 s
% 2.59/0.81  % (17485)------------------------------
% 2.59/0.81  % (17485)------------------------------
% 2.95/0.85  % (17524)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.95/0.85  % (17524)Refutation not found, incomplete strategy% (17524)------------------------------
% 2.95/0.85  % (17524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.85  % (17524)Termination reason: Refutation not found, incomplete strategy
% 2.95/0.85  
% 2.95/0.85  % (17524)Memory used [KB]: 1663
% 2.95/0.85  % (17524)Time elapsed: 0.133 s
% 2.95/0.85  % (17524)------------------------------
% 2.95/0.85  % (17524)------------------------------
% 2.95/0.89  % (17521)Refutation found. Thanks to Tanya!
% 2.95/0.89  % SZS status Theorem for theBenchmark
% 2.95/0.89  % SZS output start Proof for theBenchmark
% 2.95/0.89  fof(f1140,plain,(
% 2.95/0.89    $false),
% 2.95/0.89    inference(resolution,[],[f1137,f44])).
% 2.95/0.89  fof(f44,plain,(
% 2.95/0.89    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.95/0.89    inference(cnf_transformation,[],[f10])).
% 2.95/0.89  fof(f10,axiom,(
% 2.95/0.89    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.95/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.95/0.89  fof(f1137,plain,(
% 2.95/0.89    ( ! [X6] : (~r1_tarski(X6,k3_xboole_0(sK0,sK1))) )),
% 2.95/0.89    inference(subsumption_resolution,[],[f712,f1132])).
% 2.95/0.89  fof(f1132,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)),
% 2.95/0.89    inference(subsumption_resolution,[],[f1129,f698])).
% 2.95/0.89  fof(f698,plain,(
% 2.95/0.89    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.95/0.89    inference(global_subsumption,[],[f567,f682])).
% 2.95/0.89  fof(f682,plain,(
% 2.95/0.89    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.95/0.89    inference(subsumption_resolution,[],[f674,f69])).
% 2.95/0.89  fof(f69,plain,(
% 2.95/0.89    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.95/0.89    inference(equality_resolution,[],[f59])).
% 2.95/0.89  fof(f59,plain,(
% 2.95/0.89    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.95/0.89    inference(cnf_transformation,[],[f37])).
% 2.95/0.89  fof(f37,plain,(
% 2.95/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.95/0.89  fof(f36,plain,(
% 2.95/0.89    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.95/0.89    introduced(choice_axiom,[])).
% 2.95/0.89  fof(f35,plain,(
% 2.95/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.89    inference(rectify,[],[f34])).
% 2.95/0.89  fof(f34,plain,(
% 2.95/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.89    inference(flattening,[],[f33])).
% 2.95/0.89  fof(f33,plain,(
% 2.95/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.95/0.89    inference(nnf_transformation,[],[f4])).
% 2.95/0.89  fof(f4,axiom,(
% 2.95/0.89    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.95/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.95/0.89  fof(f674,plain,(
% 2.95/0.89    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 2.95/0.89    inference(superposition,[],[f212,f47])).
% 2.95/0.89  fof(f47,plain,(
% 2.95/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.95/0.89    inference(cnf_transformation,[],[f16])).
% 2.95/0.89  fof(f16,axiom,(
% 2.95/0.89    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.95/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.95/0.89  fof(f212,plain,(
% 2.95/0.89    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)) )),
% 2.95/0.89    inference(resolution,[],[f142,f69])).
% 2.95/0.89  fof(f142,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 2.95/0.89    inference(subsumption_resolution,[],[f134,f96])).
% 2.95/0.89  fof(f96,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.95/0.89    inference(equality_resolution,[],[f75])).
% 2.95/0.89  fof(f75,plain,(
% 2.95/0.89    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.95/0.89    inference(superposition,[],[f38,f61])).
% 2.95/0.89  fof(f61,plain,(
% 2.95/0.89    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.95/0.89    inference(cnf_transformation,[],[f37])).
% 2.95/0.89  fof(f38,plain,(
% 2.95/0.89    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.95/0.89    inference(cnf_transformation,[],[f27])).
% 2.95/0.89  fof(f27,plain,(
% 2.95/0.89    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.95/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).
% 2.95/0.89  fof(f26,plain,(
% 2.95/0.89    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.95/0.89    introduced(choice_axiom,[])).
% 2.95/0.89  fof(f22,plain,(
% 2.95/0.89    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.95/0.89    inference(ennf_transformation,[],[f18])).
% 2.95/0.89  fof(f18,negated_conjecture,(
% 2.95/0.89    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.95/0.89    inference(negated_conjecture,[],[f17])).
% 2.95/0.89  fof(f17,conjecture,(
% 2.95/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.95/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.95/0.89  fof(f134,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.95/0.89    inference(resolution,[],[f98,f68])).
% 2.95/0.89  fof(f68,plain,(
% 2.95/0.89    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.95/0.89    inference(equality_resolution,[],[f60])).
% 2.95/0.89  fof(f60,plain,(
% 2.95/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.95/0.89    inference(cnf_transformation,[],[f37])).
% 2.95/0.89  fof(f98,plain,(
% 2.95/0.89    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.95/0.89    inference(equality_resolution,[],[f76])).
% 2.95/0.89  fof(f76,plain,(
% 2.95/0.89    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 2.95/0.89    inference(superposition,[],[f38,f62])).
% 2.95/0.89  fof(f62,plain,(
% 2.95/0.89    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.95/0.89    inference(cnf_transformation,[],[f37])).
% 2.95/0.89  fof(f567,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.95/0.89    inference(duplicate_literal_removal,[],[f561])).
% 2.95/0.89  fof(f561,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.95/0.89    inference(superposition,[],[f187,f47])).
% 2.95/0.89  fof(f187,plain,(
% 2.95/0.89    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 2.95/0.89    inference(resolution,[],[f106,f68])).
% 2.95/0.89  fof(f106,plain,(
% 2.95/0.89    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.95/0.89    inference(equality_resolution,[],[f77])).
% 2.95/0.89  fof(f77,plain,(
% 2.95/0.89    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 2.95/0.89    inference(superposition,[],[f38,f63])).
% 2.95/0.89  fof(f63,plain,(
% 2.95/0.89    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.95/0.89    inference(cnf_transformation,[],[f37])).
% 2.95/0.89  fof(f1129,plain,(
% 2.95/0.89    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)),
% 2.95/0.89    inference(resolution,[],[f729,f44])).
% 2.95/0.89  fof(f729,plain,(
% 2.95/0.89    ( ! [X7] : (~r1_tarski(k3_xboole_0(sK0,sK1),X7) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)) )),
% 2.95/0.89    inference(subsumption_resolution,[],[f389,f698])).
% 2.95/0.89  fof(f389,plain,(
% 2.95/0.89    ( ! [X7] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7) | ~r1_tarski(k3_xboole_0(sK0,sK1),X7)) )),
% 2.95/0.89    inference(superposition,[],[f122,f66])).
% 2.95/0.89  fof(f66,plain,(
% 2.95/0.89    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.95/0.89    inference(definition_unfolding,[],[f55,f39])).
% 2.95/0.89  fof(f39,plain,(
% 2.95/0.89    k1_xboole_0 = o_0_0_xboole_0),
% 2.95/0.89    inference(cnf_transformation,[],[f3])).
% 2.95/0.89  fof(f3,axiom,(
% 2.95/0.89    k1_xboole_0 = o_0_0_xboole_0),
% 2.95/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 2.95/0.89  fof(f55,plain,(
% 2.95/0.89    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.95/0.89    inference(cnf_transformation,[],[f32])).
% 2.95/0.89  fof(f32,plain,(
% 2.95/0.89    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.95/0.89    inference(nnf_transformation,[],[f8])).
% 2.95/0.89  fof(f8,axiom,(
% 2.95/0.89    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.95/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.95/0.89  fof(f122,plain,(
% 2.95/0.89    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 2.95/0.89    inference(resolution,[],[f96,f68])).
% 2.95/0.89  fof(f712,plain,(
% 2.95/0.89    ( ! [X6] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | ~r1_tarski(X6,k3_xboole_0(sK0,sK1))) )),
% 2.95/0.89    inference(subsumption_resolution,[],[f240,f698])).
% 2.95/0.89  fof(f240,plain,(
% 2.95/0.89    ( ! [X6] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r1_tarski(X6,k3_xboole_0(sK0,sK1))) )),
% 2.95/0.89    inference(superposition,[],[f121,f66])).
% 2.95/0.89  fof(f121,plain,(
% 2.95/0.89    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 2.95/0.89    inference(resolution,[],[f96,f69])).
% 2.95/0.89  % SZS output end Proof for theBenchmark
% 2.95/0.89  % (17521)------------------------------
% 2.95/0.89  % (17521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.89  % (17521)Termination reason: Refutation
% 2.95/0.89  
% 2.95/0.89  % (17521)Memory used [KB]: 7164
% 2.95/0.89  % (17521)Time elapsed: 0.297 s
% 2.95/0.89  % (17521)------------------------------
% 2.95/0.89  % (17521)------------------------------
% 2.95/0.89  % (17479)Success in time 0.521 s
%------------------------------------------------------------------------------
