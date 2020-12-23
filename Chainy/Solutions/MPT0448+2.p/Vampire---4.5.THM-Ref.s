%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0448+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 ( 143 expanded)
%              Number of equality atoms :   79 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1791,f2540])).

fof(f2540,plain,(
    spl82_2 ),
    inference(avatar_contradiction_clause,[],[f2539])).

fof(f2539,plain,
    ( $false
    | spl82_2 ),
    inference(subsumption_resolution,[],[f2538,f1405])).

fof(f1405,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f673])).

fof(f673,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f2538,plain,
    ( k1_tarski(k2_tarski(sK0,sK1)) != k3_xboole_0(k1_tarski(k2_tarski(sK0,sK1)),k1_tarski(k2_tarski(sK0,sK1)))
    | spl82_2 ),
    inference(forward_demodulation,[],[f2505,f1250])).

fof(f1250,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f2505,plain,
    ( k1_tarski(k2_tarski(sK0,sK1)) != k3_xboole_0(k2_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)),k1_tarski(k2_tarski(sK0,sK1)))
    | spl82_2 ),
    inference(backward_demodulation,[],[f2448,f2474])).

fof(f2474,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f2473,f1244])).

fof(f1244,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f2473,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f2472,f1762])).

fof(f1762,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f1678,f1269])).

fof(f1269,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f650])).

fof(f650,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

fof(f1678,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f1298])).

fof(f1298,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f752])).

fof(f752,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f751])).

fof(f751,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f661])).

fof(f661,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f2472,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0,X1))),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f2471,f1761])).

fof(f1761,plain,(
    ! [X0,X1] : k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f1677,f1269])).

fof(f1677,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f1299])).

fof(f1299,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f752])).

fof(f2471,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0,X1))),k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) ),
    inference(unit_resulting_resolution,[],[f1269,f1113])).

fof(f1113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f681])).

fof(f681,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f2448,plain,
    ( k1_tarski(k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))) != k3_xboole_0(k2_tarski(k2_tarski(sK0,sK1),k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),k1_tarski(k2_tarski(sK0,sK1)))
    | spl82_2 ),
    inference(forward_demodulation,[],[f2414,f1247])).

fof(f1247,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f2414,plain,
    ( k1_tarski(k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))) != k3_xboole_0(k2_tarski(k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))),k2_tarski(sK0,sK1)),k1_tarski(k2_tarski(sK0,sK1)))
    | spl82_2 ),
    inference(unit_resulting_resolution,[],[f1790,f1639,f1187])).

fof(f1187,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f703])).

fof(f703,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | ~ r2_hidden(X1,X2)
      | k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f417])).

fof(f417,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f1639,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1638])).

fof(f1638,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f1119])).

fof(f1119,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f930])).

fof(f930,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f928,f929])).

fof(f929,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f928,plain,(
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
    inference(rectify,[],[f927])).

fof(f927,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1790,plain,
    ( k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))
    | spl82_2 ),
    inference(avatar_component_clause,[],[f1788])).

fof(f1788,plain,
    ( spl82_2
  <=> k2_tarski(sK0,sK1) = k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl82_2])])).

fof(f1791,plain,(
    ~ spl82_2 ),
    inference(avatar_split_clause,[],[f1109,f1788])).

fof(f1109,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f924])).

fof(f924,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f676,f923])).

fof(f923,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f676,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f670])).

fof(f670,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f669])).

fof(f669,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
