%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0094+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  52 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f921,plain,(
    $false ),
    inference(subsumption_resolution,[],[f336,f869])).

fof(f869,plain,(
    ! [X10] : k4_xboole_0(k2_xboole_0(sK3,X10),sK2) = k2_xboole_0(sK3,k4_xboole_0(X10,sK2)) ),
    inference(superposition,[],[f234,f404])).

fof(f404,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f349,f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f349,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f211,f271])).

fof(f271,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f211,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK2),sK3) != k4_xboole_0(k2_xboole_0(sK4,sK3),sK2)
    & r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f140,f198])).

fof(f198,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
        & r1_xboole_0(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK4,sK2),sK3) != k4_xboole_0(k2_xboole_0(sK4,sK3),sK2)
      & r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f140,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f134])).

fof(f134,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f133])).

fof(f133,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f234,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f336,plain,(
    k4_xboole_0(k2_xboole_0(sK3,sK4),sK2) != k2_xboole_0(sK3,k4_xboole_0(sK4,sK2)) ),
    inference(forward_demodulation,[],[f335,f226])).

fof(f226,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f335,plain,(
    k2_xboole_0(k4_xboole_0(sK4,sK2),sK3) != k4_xboole_0(k2_xboole_0(sK3,sK4),sK2) ),
    inference(forward_demodulation,[],[f212,f226])).

fof(f212,plain,(
    k2_xboole_0(k4_xboole_0(sK4,sK2),sK3) != k4_xboole_0(k2_xboole_0(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f199])).
%------------------------------------------------------------------------------
