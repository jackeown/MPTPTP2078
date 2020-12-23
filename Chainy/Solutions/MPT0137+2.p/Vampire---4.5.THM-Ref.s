%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0137+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  13 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f853,plain,(
    $false ),
    inference(resolution,[],[f810,f687])).

fof(f687,plain,(
    ~ sQ24_eqProxy(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))) ),
    inference(equality_proxy_replacement,[],[f390,f676])).

fof(f676,plain,(
    ! [X1,X0] :
      ( sQ24_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ24_eqProxy])])).

fof(f390,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f315])).

fof(f315,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f206,f314])).

fof(f314,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f206,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(ennf_transformation,[],[f199])).

fof(f199,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(negated_conjecture,[],[f198])).

fof(f198,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

fof(f810,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sQ24_eqProxy(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ),
    inference(equality_proxy_replacement,[],[f644,f676])).

fof(f644,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
%------------------------------------------------------------------------------
