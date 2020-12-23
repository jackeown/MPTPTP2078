%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:21 EST 2020

% Result     : Theorem 5.47s
% Output     : Refutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 218 expanded)
%              Number of leaves         :    8 (  62 expanded)
%              Depth                    :   21
%              Number of atoms          :  175 ( 454 expanded)
%              Number of equality atoms :   69 ( 239 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4394,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4393,f42])).

fof(f42,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f18,f41,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f4393,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f4392,f62])).

fof(f62,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f23,f41])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f4392,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f4391,f17])).

fof(f17,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f4391,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f4385,f80])).

fof(f80,plain,(
    r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f79,f62])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f69,f43])).

fof(f43,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f16,f21,f41])).

fof(f16,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f21])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f4385,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f59,f4366])).

fof(f4366,plain,(
    sK3 = sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f4357,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4357,plain,(
    r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(subsumption_resolution,[],[f4356,f42])).

fof(f4356,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(duplicate_literal_removal,[],[f4351])).

fof(f4351,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f4330,f116])).

fof(f116,plain,(
    ! [X26,X25] :
      ( ~ r2_hidden(sK6(X25,sK2,X26),sK1)
      | k4_xboole_0(X25,k4_xboole_0(X25,sK2)) = X26
      | r2_hidden(sK6(X25,sK2,X26),k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(sK6(X25,sK2,X26),X26) ) ),
    inference(resolution,[],[f57,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f68,f43])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f39,f21])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f36,f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f4330,plain,(
    ! [X36] :
      ( r2_hidden(sK6(sK0,X36,k2_enumset1(sK3,sK3,sK3,sK3)),sK1)
      | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,X36)) ) ),
    inference(duplicate_literal_removal,[],[f4317])).

fof(f4317,plain,(
    ! [X36] :
      ( r2_hidden(sK6(sK0,X36,k2_enumset1(sK3,sK3,sK3,sK3)),sK1)
      | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,X36))
      | r2_hidden(sK6(sK0,X36,k2_enumset1(sK3,sK3,sK3,sK3)),sK1) ) ),
    inference(resolution,[],[f4243,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f70,f43])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f4243,plain,(
    ! [X17,X18] :
      ( r2_hidden(sK6(sK0,X17,X18),X18)
      | r2_hidden(sK6(sK0,X17,X18),sK1)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X17)) = X18 ) ),
    inference(superposition,[],[f145,f326])).

fof(f326,plain,(
    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f296,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X1),X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ) ),
    inference(factoring,[],[f57])).

fof(f296,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK6(sK1,X7,X7),sK0)
      | k4_xboole_0(sK1,k4_xboole_0(sK1,X7)) = X7 ) ),
    inference(resolution,[],[f286,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f286,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK6(X9,X10,X10),X9)
      | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10 ) ),
    inference(subsumption_resolution,[],[f282,f57])).

fof(f282,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK6(X9,X10,X10),X9)
      | ~ r2_hidden(sK6(X9,X10,X10),X10)
      | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10 ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK6(X9,X10,X10),X9)
      | ~ r2_hidden(sK6(X9,X10,X10),X10)
      | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10
      | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10 ) ),
    inference(resolution,[],[f59,f127])).

fof(f145,plain,(
    ! [X14,X12,X13,X11] :
      ( r2_hidden(sK6(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13,X14),X14)
      | r2_hidden(sK6(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13,X14),X11)
      | k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13)) = X14 ) ),
    inference(resolution,[],[f58,f70])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f35,f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f34,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:42:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.49  % (17391)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (17392)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (17415)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.51  % (17404)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.52  % (17389)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (17398)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (17397)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (17390)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.54  % (17414)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (17394)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (17388)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (17393)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (17409)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.54  % (17399)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.54  % (17405)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (17413)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.55  % (17400)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.55  % (17411)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.55  % (17402)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.55  % (17387)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.55  % (17403)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.55  % (17410)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.55  % (17386)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.55  % (17396)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.55  % (17408)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.56  % (17401)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.56  % (17407)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.56  % (17406)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.56  % (17395)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.59  % (17412)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 3.36/0.80  % (17391)Time limit reached!
% 3.36/0.80  % (17391)------------------------------
% 3.36/0.80  % (17391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.80  % (17391)Termination reason: Time limit
% 3.36/0.80  % (17391)Termination phase: Saturation
% 3.36/0.80  
% 3.36/0.80  % (17391)Memory used [KB]: 9083
% 3.36/0.80  % (17391)Time elapsed: 0.400 s
% 3.36/0.80  % (17391)------------------------------
% 3.36/0.80  % (17391)------------------------------
% 4.23/0.89  % (17396)Time limit reached!
% 4.23/0.89  % (17396)------------------------------
% 4.23/0.89  % (17396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.23/0.89  % (17427)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.23/0.90  % (17396)Termination reason: Time limit
% 4.23/0.90  % (17396)Termination phase: Saturation
% 4.23/0.90  
% 4.23/0.90  % (17396)Memory used [KB]: 18549
% 4.23/0.90  % (17396)Time elapsed: 0.500 s
% 4.23/0.90  % (17396)------------------------------
% 4.23/0.90  % (17396)------------------------------
% 4.23/0.90  % (17403)Time limit reached!
% 4.23/0.90  % (17403)------------------------------
% 4.23/0.90  % (17403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.23/0.90  % (17403)Termination reason: Time limit
% 4.23/0.90  
% 4.23/0.90  % (17403)Memory used [KB]: 13688
% 4.23/0.90  % (17403)Time elapsed: 0.509 s
% 4.23/0.90  % (17403)------------------------------
% 4.23/0.90  % (17403)------------------------------
% 4.23/0.91  % (17398)Time limit reached!
% 4.23/0.91  % (17398)------------------------------
% 4.23/0.91  % (17398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.23/0.91  % (17398)Termination reason: Time limit
% 4.23/0.91  
% 4.23/0.91  % (17398)Memory used [KB]: 8187
% 4.23/0.91  % (17398)Time elapsed: 0.502 s
% 4.23/0.91  % (17398)------------------------------
% 4.23/0.91  % (17398)------------------------------
% 4.23/0.91  % (17386)Time limit reached!
% 4.23/0.91  % (17386)------------------------------
% 4.23/0.91  % (17386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.23/0.91  % (17386)Termination reason: Time limit
% 4.23/0.91  
% 4.23/0.91  % (17386)Memory used [KB]: 3709
% 4.23/0.91  % (17386)Time elapsed: 0.519 s
% 4.23/0.91  % (17386)------------------------------
% 4.23/0.91  % (17386)------------------------------
% 4.43/0.92  % (17387)Time limit reached!
% 4.43/0.92  % (17387)------------------------------
% 4.43/0.92  % (17387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.92  % (17387)Termination reason: Time limit
% 4.43/0.92  
% 4.43/0.92  % (17387)Memory used [KB]: 8187
% 4.43/0.92  % (17387)Time elapsed: 0.506 s
% 4.43/0.92  % (17387)------------------------------
% 4.43/0.92  % (17387)------------------------------
% 4.51/0.99  % (17414)Time limit reached!
% 4.51/0.99  % (17414)------------------------------
% 4.51/0.99  % (17414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.99  % (17414)Termination reason: Time limit
% 4.51/0.99  % (17414)Termination phase: Saturation
% 4.51/0.99  
% 4.51/0.99  % (17414)Memory used [KB]: 8315
% 4.51/0.99  % (17414)Time elapsed: 0.600 s
% 4.51/0.99  % (17414)------------------------------
% 4.51/0.99  % (17414)------------------------------
% 5.04/1.02  % (17431)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.04/1.02  % (17402)Time limit reached!
% 5.04/1.02  % (17402)------------------------------
% 5.04/1.02  % (17402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.02  % (17402)Termination reason: Time limit
% 5.04/1.02  
% 5.04/1.02  % (17402)Memory used [KB]: 15991
% 5.04/1.02  % (17402)Time elapsed: 0.624 s
% 5.04/1.02  % (17402)------------------------------
% 5.04/1.02  % (17402)------------------------------
% 5.04/1.02  % (17393)Time limit reached!
% 5.04/1.02  % (17393)------------------------------
% 5.04/1.02  % (17393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.02  % (17393)Termination reason: Time limit
% 5.04/1.02  
% 5.04/1.02  % (17393)Memory used [KB]: 9722
% 5.04/1.02  % (17393)Time elapsed: 0.603 s
% 5.04/1.02  % (17393)------------------------------
% 5.04/1.02  % (17393)------------------------------
% 5.04/1.02  % (17440)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.04/1.03  % (17445)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.04/1.03  % (17433)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.04/1.05  % (17441)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.47/1.11  % (17392)Refutation found. Thanks to Tanya!
% 5.47/1.11  % SZS status Theorem for theBenchmark
% 5.47/1.11  % SZS output start Proof for theBenchmark
% 5.47/1.11  fof(f4394,plain,(
% 5.47/1.11    $false),
% 5.47/1.11    inference(subsumption_resolution,[],[f4393,f42])).
% 5.47/1.11  fof(f42,plain,(
% 5.47/1.11    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.47/1.11    inference(definition_unfolding,[],[f18,f41,f21])).
% 5.47/1.11  fof(f21,plain,(
% 5.47/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.47/1.11    inference(cnf_transformation,[],[f3])).
% 5.47/1.11  fof(f3,axiom,(
% 5.47/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.47/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.47/1.11  fof(f41,plain,(
% 5.47/1.11    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 5.47/1.11    inference(definition_unfolding,[],[f19,f40])).
% 5.47/1.11  fof(f40,plain,(
% 5.47/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 5.47/1.11    inference(definition_unfolding,[],[f20,f27])).
% 5.47/1.11  fof(f27,plain,(
% 5.47/1.11    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.47/1.11    inference(cnf_transformation,[],[f8])).
% 5.47/1.11  fof(f8,axiom,(
% 5.47/1.11    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.47/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 5.47/1.11  fof(f20,plain,(
% 5.47/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 5.47/1.11    inference(cnf_transformation,[],[f7])).
% 5.47/1.11  fof(f7,axiom,(
% 5.47/1.11    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 5.47/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 5.47/1.11  fof(f19,plain,(
% 5.47/1.11    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.47/1.11    inference(cnf_transformation,[],[f6])).
% 5.47/1.12  fof(f6,axiom,(
% 5.47/1.12    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.47/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 5.47/1.12  fof(f18,plain,(
% 5.47/1.12    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 5.47/1.12    inference(cnf_transformation,[],[f13])).
% 5.47/1.12  fof(f13,plain,(
% 5.47/1.12    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 5.47/1.12    inference(flattening,[],[f12])).
% 5.47/1.12  fof(f12,plain,(
% 5.47/1.12    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 5.47/1.12    inference(ennf_transformation,[],[f10])).
% 5.47/1.12  fof(f10,negated_conjecture,(
% 5.47/1.12    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 5.47/1.12    inference(negated_conjecture,[],[f9])).
% 5.47/1.12  fof(f9,conjecture,(
% 5.47/1.12    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 5.47/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 5.47/1.12  fof(f4393,plain,(
% 5.47/1.12    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.47/1.12    inference(subsumption_resolution,[],[f4392,f62])).
% 5.47/1.12  fof(f62,plain,(
% 5.47/1.12    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 5.47/1.12    inference(equality_resolution,[],[f61])).
% 5.47/1.12  fof(f61,plain,(
% 5.47/1.12    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 5.47/1.12    inference(equality_resolution,[],[f47])).
% 5.47/1.12  fof(f47,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 5.47/1.12    inference(definition_unfolding,[],[f23,f41])).
% 5.47/1.12  fof(f23,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 5.47/1.12    inference(cnf_transformation,[],[f4])).
% 5.47/1.12  fof(f4,axiom,(
% 5.47/1.12    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 5.47/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 5.47/1.12  fof(f4392,plain,(
% 5.47/1.12    ~r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.47/1.12    inference(subsumption_resolution,[],[f4391,f17])).
% 5.47/1.12  fof(f17,plain,(
% 5.47/1.12    r2_hidden(sK3,sK0)),
% 5.47/1.12    inference(cnf_transformation,[],[f13])).
% 5.47/1.12  fof(f4391,plain,(
% 5.47/1.12    ~r2_hidden(sK3,sK0) | ~r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.47/1.12    inference(subsumption_resolution,[],[f4385,f80])).
% 5.47/1.12  fof(f80,plain,(
% 5.47/1.12    r2_hidden(sK3,sK2)),
% 5.47/1.12    inference(resolution,[],[f79,f62])).
% 5.47/1.12  fof(f79,plain,(
% 5.47/1.12    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(X0,sK2)) )),
% 5.47/1.12    inference(superposition,[],[f69,f43])).
% 5.47/1.12  fof(f43,plain,(
% 5.47/1.12    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 5.47/1.12    inference(definition_unfolding,[],[f16,f21,f41])).
% 5.47/1.12  fof(f16,plain,(
% 5.47/1.12    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 5.47/1.12    inference(cnf_transformation,[],[f13])).
% 5.47/1.12  fof(f69,plain,(
% 5.47/1.12    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 5.47/1.12    inference(equality_resolution,[],[f55])).
% 5.47/1.12  fof(f55,plain,(
% 5.47/1.12    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 5.47/1.12    inference(definition_unfolding,[],[f38,f21])).
% 5.47/1.12  fof(f38,plain,(
% 5.47/1.12    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.47/1.12    inference(cnf_transformation,[],[f2])).
% 5.47/1.12  fof(f2,axiom,(
% 5.47/1.12    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.47/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 5.47/1.12  fof(f4385,plain,(
% 5.47/1.12    ~r2_hidden(sK3,sK2) | ~r2_hidden(sK3,sK0) | ~r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.47/1.12    inference(superposition,[],[f59,f4366])).
% 5.47/1.12  fof(f4366,plain,(
% 5.47/1.12    sK3 = sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 5.47/1.12    inference(resolution,[],[f4357,f60])).
% 5.47/1.12  fof(f60,plain,(
% 5.47/1.12    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 5.47/1.12    inference(equality_resolution,[],[f46])).
% 5.47/1.12  fof(f46,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 5.47/1.12    inference(definition_unfolding,[],[f24,f41])).
% 5.47/1.12  fof(f24,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 5.47/1.12    inference(cnf_transformation,[],[f4])).
% 5.47/1.12  fof(f4357,plain,(
% 5.47/1.12    r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 5.47/1.12    inference(subsumption_resolution,[],[f4356,f42])).
% 5.47/1.12  fof(f4356,plain,(
% 5.47/1.12    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 5.47/1.12    inference(duplicate_literal_removal,[],[f4351])).
% 5.47/1.12  fof(f4351,plain,(
% 5.47/1.12    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(sK6(sK0,sK2,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 5.47/1.12    inference(resolution,[],[f4330,f116])).
% 5.47/1.12  fof(f116,plain,(
% 5.47/1.12    ( ! [X26,X25] : (~r2_hidden(sK6(X25,sK2,X26),sK1) | k4_xboole_0(X25,k4_xboole_0(X25,sK2)) = X26 | r2_hidden(sK6(X25,sK2,X26),k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(sK6(X25,sK2,X26),X26)) )),
% 5.47/1.12    inference(resolution,[],[f57,f95])).
% 5.47/1.12  fof(f95,plain,(
% 5.47/1.12    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,sK1)) )),
% 5.47/1.12    inference(superposition,[],[f68,f43])).
% 5.47/1.12  fof(f68,plain,(
% 5.47/1.12    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 5.47/1.12    inference(equality_resolution,[],[f54])).
% 5.47/1.12  fof(f54,plain,(
% 5.47/1.12    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 5.47/1.12    inference(definition_unfolding,[],[f39,f21])).
% 5.47/1.12  fof(f39,plain,(
% 5.47/1.12    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.47/1.12    inference(cnf_transformation,[],[f2])).
% 5.47/1.12  fof(f57,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 5.47/1.12    inference(definition_unfolding,[],[f36,f21])).
% 5.47/1.12  fof(f36,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.47/1.12    inference(cnf_transformation,[],[f2])).
% 5.47/1.12  fof(f4330,plain,(
% 5.47/1.12    ( ! [X36] : (r2_hidden(sK6(sK0,X36,k2_enumset1(sK3,sK3,sK3,sK3)),sK1) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,X36))) )),
% 5.47/1.12    inference(duplicate_literal_removal,[],[f4317])).
% 5.47/1.12  fof(f4317,plain,(
% 5.47/1.12    ( ! [X36] : (r2_hidden(sK6(sK0,X36,k2_enumset1(sK3,sK3,sK3,sK3)),sK1) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,X36)) | r2_hidden(sK6(sK0,X36,k2_enumset1(sK3,sK3,sK3,sK3)),sK1)) )),
% 5.47/1.12    inference(resolution,[],[f4243,f84])).
% 5.47/1.12  fof(f84,plain,(
% 5.47/1.12    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(X0,sK1)) )),
% 5.47/1.12    inference(superposition,[],[f70,f43])).
% 5.47/1.12  fof(f70,plain,(
% 5.47/1.12    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 5.47/1.12    inference(equality_resolution,[],[f56])).
% 5.47/1.12  fof(f56,plain,(
% 5.47/1.12    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 5.47/1.12    inference(definition_unfolding,[],[f37,f21])).
% 5.47/1.12  fof(f37,plain,(
% 5.47/1.12    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.47/1.12    inference(cnf_transformation,[],[f2])).
% 5.47/1.12  fof(f4243,plain,(
% 5.47/1.12    ( ! [X17,X18] : (r2_hidden(sK6(sK0,X17,X18),X18) | r2_hidden(sK6(sK0,X17,X18),sK1) | k4_xboole_0(sK0,k4_xboole_0(sK0,X17)) = X18) )),
% 5.47/1.12    inference(superposition,[],[f145,f326])).
% 5.47/1.12  fof(f326,plain,(
% 5.47/1.12    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 5.47/1.12    inference(duplicate_literal_removal,[],[f325])).
% 5.47/1.12  fof(f325,plain,(
% 5.47/1.12    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 5.47/1.12    inference(resolution,[],[f296,f127])).
% 5.47/1.12  fof(f127,plain,(
% 5.47/1.12    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X1),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1) )),
% 5.47/1.12    inference(factoring,[],[f57])).
% 5.47/1.12  fof(f296,plain,(
% 5.47/1.12    ( ! [X7] : (~r2_hidden(sK6(sK1,X7,X7),sK0) | k4_xboole_0(sK1,k4_xboole_0(sK1,X7)) = X7) )),
% 5.47/1.12    inference(resolution,[],[f286,f74])).
% 5.47/1.12  fof(f74,plain,(
% 5.47/1.12    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 5.47/1.12    inference(resolution,[],[f22,f15])).
% 5.47/1.12  fof(f15,plain,(
% 5.47/1.12    r1_tarski(sK0,sK1)),
% 5.47/1.12    inference(cnf_transformation,[],[f13])).
% 5.47/1.12  fof(f22,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 5.47/1.12    inference(cnf_transformation,[],[f14])).
% 5.47/1.12  fof(f14,plain,(
% 5.47/1.12    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 5.47/1.12    inference(ennf_transformation,[],[f11])).
% 5.47/1.12  fof(f11,plain,(
% 5.47/1.12    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.47/1.12    inference(unused_predicate_definition_removal,[],[f1])).
% 5.47/1.12  fof(f1,axiom,(
% 5.47/1.12    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.47/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 5.47/1.12  fof(f286,plain,(
% 5.47/1.12    ( ! [X10,X9] : (~r2_hidden(sK6(X9,X10,X10),X9) | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10) )),
% 5.47/1.12    inference(subsumption_resolution,[],[f282,f57])).
% 5.47/1.12  fof(f282,plain,(
% 5.47/1.12    ( ! [X10,X9] : (~r2_hidden(sK6(X9,X10,X10),X9) | ~r2_hidden(sK6(X9,X10,X10),X10) | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10) )),
% 5.47/1.12    inference(duplicate_literal_removal,[],[f271])).
% 5.47/1.12  fof(f271,plain,(
% 5.47/1.12    ( ! [X10,X9] : (~r2_hidden(sK6(X9,X10,X10),X9) | ~r2_hidden(sK6(X9,X10,X10),X10) | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10 | k4_xboole_0(X9,k4_xboole_0(X9,X10)) = X10) )),
% 5.47/1.12    inference(resolution,[],[f59,f127])).
% 5.47/1.12  fof(f145,plain,(
% 5.47/1.12    ( ! [X14,X12,X13,X11] : (r2_hidden(sK6(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13,X14),X14) | r2_hidden(sK6(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13,X14),X11) | k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13)) = X14) )),
% 5.47/1.12    inference(resolution,[],[f58,f70])).
% 5.47/1.12  fof(f58,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 5.47/1.12    inference(definition_unfolding,[],[f35,f21])).
% 5.47/1.12  fof(f35,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.47/1.12    inference(cnf_transformation,[],[f2])).
% 5.47/1.12  fof(f59,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 5.47/1.12    inference(definition_unfolding,[],[f34,f21])).
% 5.47/1.12  fof(f34,plain,(
% 5.47/1.12    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.47/1.12    inference(cnf_transformation,[],[f2])).
% 5.47/1.12  % SZS output end Proof for theBenchmark
% 5.47/1.12  % (17392)------------------------------
% 5.47/1.12  % (17392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.47/1.12  % (17392)Termination reason: Refutation
% 5.47/1.12  
% 5.47/1.12  % (17392)Memory used [KB]: 12025
% 5.47/1.12  % (17392)Time elapsed: 0.686 s
% 5.47/1.12  % (17392)------------------------------
% 5.47/1.12  % (17392)------------------------------
% 5.47/1.12  % (17380)Success in time 0.776 s
%------------------------------------------------------------------------------
