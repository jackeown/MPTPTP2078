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
% DateTime   : Thu Dec  3 12:31:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 145 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 175 expanded)
%              Number of equality atoms :   61 ( 136 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1069,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f795,f1003,f1068])).

fof(f1068,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f1067])).

fof(f1067,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f1064,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1064,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | spl3_6 ),
    inference(superposition,[],[f1002,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1002,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl3_6
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1003,plain,
    ( ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f822,f792,f1000])).

fof(f792,plain,
    ( spl3_2
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f822,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl3_2 ),
    inference(forward_demodulation,[],[f821,f350])).

fof(f350,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f109,f34])).

fof(f109,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f821,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | spl3_2 ),
    inference(forward_demodulation,[],[f820,f757])).

fof(f757,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f716,f698])).

fof(f698,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f654,f350])).

fof(f654,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) ),
    inference(superposition,[],[f111,f46])).

fof(f111,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f42,f46])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f716,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f129,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f129,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f125,f32])).

fof(f125,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(unit_resulting_resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f820,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f817,f391])).

fof(f391,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f75,f32])).

fof(f75,plain,(
    ! [X6,X4,X5] : k2_xboole_0(X6,k4_xboole_0(X4,X5)) = k2_xboole_0(X6,k4_xboole_0(X4,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f817,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl3_2 ),
    inference(superposition,[],[f794,f85])).

fof(f85,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f42,f32])).

fof(f794,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f792])).

fof(f795,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f765,f147,f792])).

fof(f147,plain,
    ( spl3_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f765,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f764,f30])).

fof(f764,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k2_xboole_0(sK0,sK0))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f763,f41])).

fof(f763,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f759,f400])).

fof(f400,plain,(
    ! [X37,X38,X36] : k2_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X38,k4_xboole_0(X36,k4_xboole_0(X36,X37)))) = k2_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X38,X36)) ),
    inference(superposition,[],[f75,f46])).

fof(f759,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(backward_demodulation,[],[f149,f717])).

fof(f717,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X4,X3))) = k4_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f129,f32])).

fof(f149,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f150,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f97,f147])).

fof(f97,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f49,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f42,f30])).

fof(f49,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f44,f41])).

fof(f44,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f27,f36,f36,f33])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:25:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (3809)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.50  % (3808)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (3807)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.50  % (3811)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.50  % (3820)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.50  % (3812)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.50  % (3818)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.51  % (3815)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.51  % (3819)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.51  % (3816)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.51  % (3817)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.51  % (3816)Refutation not found, incomplete strategy% (3816)------------------------------
% 0.23/0.51  % (3816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (3816)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (3816)Memory used [KB]: 10618
% 0.23/0.51  % (3816)Time elapsed: 0.065 s
% 0.23/0.51  % (3816)------------------------------
% 0.23/0.51  % (3816)------------------------------
% 0.23/0.51  % (3821)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.51  % (3822)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.52  % (3810)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.53  % (3814)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.53  % (3806)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.53  % (3805)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.55  % (3813)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.57  % (3820)Refutation found. Thanks to Tanya!
% 0.23/0.57  % SZS status Theorem for theBenchmark
% 0.23/0.57  % SZS output start Proof for theBenchmark
% 0.23/0.57  fof(f1069,plain,(
% 0.23/0.57    $false),
% 0.23/0.57    inference(avatar_sat_refutation,[],[f150,f795,f1003,f1068])).
% 0.23/0.57  fof(f1068,plain,(
% 0.23/0.57    spl3_6),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f1067])).
% 0.23/0.57  fof(f1067,plain,(
% 0.23/0.57    $false | spl3_6),
% 0.23/0.57    inference(subsumption_resolution,[],[f1064,f34])).
% 0.23/0.57  fof(f34,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f5])).
% 0.23/0.57  fof(f5,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.23/0.57  fof(f1064,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | spl3_6),
% 0.23/0.57    inference(superposition,[],[f1002,f32])).
% 0.23/0.57  fof(f32,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f1])).
% 0.23/0.57  fof(f1,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.57  fof(f1002,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl3_6),
% 0.23/0.57    inference(avatar_component_clause,[],[f1000])).
% 0.23/0.57  fof(f1000,plain,(
% 0.23/0.57    spl3_6 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.57  fof(f1003,plain,(
% 0.23/0.57    ~spl3_6 | spl3_2),
% 0.23/0.57    inference(avatar_split_clause,[],[f822,f792,f1000])).
% 0.23/0.57  fof(f792,plain,(
% 0.23/0.57    spl3_2 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.57  fof(f822,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl3_2),
% 0.23/0.57    inference(forward_demodulation,[],[f821,f350])).
% 0.23/0.57  fof(f350,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 0.23/0.57    inference(superposition,[],[f109,f34])).
% 0.23/0.57  fof(f109,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 0.23/0.57    inference(superposition,[],[f46,f32])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.57    inference(definition_unfolding,[],[f35,f33])).
% 0.23/0.57  fof(f33,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f7])).
% 0.23/0.57  fof(f7,axiom,(
% 0.23/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.57  fof(f35,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.57    inference(cnf_transformation,[],[f10])).
% 0.23/0.57  fof(f10,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.23/0.57  fof(f821,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | spl3_2),
% 0.23/0.57    inference(forward_demodulation,[],[f820,f757])).
% 0.23/0.57  fof(f757,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.23/0.57    inference(forward_demodulation,[],[f716,f698])).
% 0.23/0.57  fof(f698,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.57    inference(forward_demodulation,[],[f654,f350])).
% 0.23/0.57  fof(f654,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0)) )),
% 0.23/0.57    inference(superposition,[],[f111,f46])).
% 0.23/0.57  fof(f111,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.23/0.57    inference(superposition,[],[f42,f46])).
% 0.23/0.57  fof(f42,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f9])).
% 0.23/0.57  fof(f9,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.23/0.57  fof(f716,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.23/0.57    inference(superposition,[],[f129,f30])).
% 0.23/0.57  fof(f30,plain,(
% 0.23/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.23/0.57    inference(cnf_transformation,[],[f17])).
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.23/0.57    inference(rectify,[],[f3])).
% 0.23/0.57  fof(f3,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.23/0.57  fof(f129,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 0.23/0.57    inference(forward_demodulation,[],[f125,f32])).
% 0.23/0.57  fof(f125,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f31,f43])).
% 0.23/0.57  fof(f43,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f21])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f13])).
% 0.23/0.57  fof(f13,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f11])).
% 0.23/0.57  fof(f11,axiom,(
% 0.23/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.23/0.57  fof(f820,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) | spl3_2),
% 0.23/0.57    inference(forward_demodulation,[],[f817,f391])).
% 0.23/0.57  fof(f391,plain,(
% 0.23/0.57    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 0.23/0.57    inference(superposition,[],[f75,f32])).
% 0.23/0.57  fof(f75,plain,(
% 0.23/0.57    ( ! [X6,X4,X5] : (k2_xboole_0(X6,k4_xboole_0(X4,X5)) = k2_xboole_0(X6,k4_xboole_0(X4,k2_xboole_0(X5,X6)))) )),
% 0.23/0.57    inference(superposition,[],[f34,f41])).
% 0.23/0.57  fof(f41,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.57  fof(f817,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl3_2),
% 0.23/0.57    inference(superposition,[],[f794,f85])).
% 0.23/0.57  fof(f85,plain,(
% 0.23/0.57    ( ! [X4,X2,X3] : (k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4)) )),
% 0.23/0.57    inference(superposition,[],[f42,f32])).
% 0.23/0.57  fof(f794,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_2),
% 0.23/0.57    inference(avatar_component_clause,[],[f792])).
% 0.23/0.57  fof(f795,plain,(
% 0.23/0.57    ~spl3_2 | spl3_1),
% 0.23/0.57    inference(avatar_split_clause,[],[f765,f147,f792])).
% 0.23/0.57  fof(f147,plain,(
% 0.23/0.57    spl3_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.57  fof(f765,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 0.23/0.57    inference(forward_demodulation,[],[f764,f30])).
% 0.23/0.57  fof(f764,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k2_xboole_0(sK0,sK0))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 0.23/0.57    inference(forward_demodulation,[],[f763,f41])).
% 0.23/0.57  fof(f763,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 0.23/0.57    inference(forward_demodulation,[],[f759,f400])).
% 0.23/0.57  fof(f400,plain,(
% 0.23/0.57    ( ! [X37,X38,X36] : (k2_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X38,k4_xboole_0(X36,k4_xboole_0(X36,X37)))) = k2_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X38,X36))) )),
% 0.23/0.57    inference(superposition,[],[f75,f46])).
% 0.23/0.57  fof(f759,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 0.23/0.57    inference(backward_demodulation,[],[f149,f717])).
% 0.23/0.57  fof(f717,plain,(
% 0.23/0.57    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X4,X3))) = k4_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X4,X3))) )),
% 0.23/0.57    inference(superposition,[],[f129,f32])).
% 0.23/0.57  fof(f149,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 0.23/0.57    inference(avatar_component_clause,[],[f147])).
% 0.23/0.57  fof(f150,plain,(
% 0.23/0.57    ~spl3_1),
% 0.23/0.57    inference(avatar_split_clause,[],[f97,f147])).
% 0.23/0.57  fof(f97,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.23/0.57    inference(backward_demodulation,[],[f49,f84])).
% 0.23/0.57  fof(f84,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.57    inference(superposition,[],[f42,f30])).
% 0.23/0.57  fof(f49,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.23/0.57    inference(backward_demodulation,[],[f44,f41])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.23/0.57    inference(definition_unfolding,[],[f27,f36,f36,f33])).
% 0.23/0.57  fof(f36,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f2])).
% 0.23/0.57  fof(f2,axiom,(
% 0.23/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.23/0.57  fof(f27,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.23/0.57    inference(cnf_transformation,[],[f23])).
% 0.23/0.57  fof(f23,plain,(
% 0.23/0.57    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 0.23/0.57  fof(f22,plain,(
% 0.23/0.57    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f19,plain,(
% 0.23/0.57    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f16])).
% 0.23/0.57  fof(f16,negated_conjecture,(
% 0.23/0.57    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.57    inference(negated_conjecture,[],[f15])).
% 0.23/0.57  fof(f15,conjecture,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.23/0.57  % SZS output end Proof for theBenchmark
% 0.23/0.57  % (3820)------------------------------
% 0.23/0.57  % (3820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (3820)Termination reason: Refutation
% 0.23/0.57  
% 0.23/0.57  % (3820)Memory used [KB]: 12025
% 0.23/0.57  % (3820)Time elapsed: 0.137 s
% 0.23/0.57  % (3820)------------------------------
% 0.23/0.57  % (3820)------------------------------
% 0.23/0.57  % (3804)Success in time 0.198 s
%------------------------------------------------------------------------------
