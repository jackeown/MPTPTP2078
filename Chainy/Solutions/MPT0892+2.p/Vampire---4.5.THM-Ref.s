%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0892+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   20 (  61 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 165 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2064,plain,(
    $false ),
    inference(global_subsumption,[],[f2027,f2033,f2032])).

fof(f2032,plain,(
    ~ r1_xboole_0(sK0,sK3) ),
    inference(unit_resulting_resolution,[],[f1973,f1614])).

fof(f1614,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1359])).

fof(f1359,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f343])).

fof(f343,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1973,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f1892,f1614])).

fof(f1892,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f1612,f1683,f1683])).

fof(f1683,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f1612,plain,(
    ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f1535])).

fof(f1535,plain,
    ( ( r1_xboole_0(sK2,sK5)
      | r1_xboole_0(sK1,sK4)
      | r1_xboole_0(sK0,sK3) )
    & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1358,f1534])).

fof(f1534,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( r1_xboole_0(X2,X5)
          | r1_xboole_0(X1,X4)
          | r1_xboole_0(X0,X3) )
        & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
   => ( ( r1_xboole_0(sK2,sK5)
        | r1_xboole_0(sK1,sK4)
        | r1_xboole_0(sK0,sK3) )
      & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f1358,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( r1_xboole_0(X2,X5)
        | r1_xboole_0(X1,X4)
        | r1_xboole_0(X0,X3) )
      & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f1348])).

fof(f1348,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
       => ( ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f1347])).

fof(f1347,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_mcart_1)).

fof(f2033,plain,(
    ~ r1_xboole_0(sK1,sK4) ),
    inference(unit_resulting_resolution,[],[f1973,f1615])).

fof(f1615,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f1359])).

fof(f2027,plain,
    ( r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f1974,f1613])).

fof(f1613,plain,
    ( r1_xboole_0(sK2,sK5)
    | r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f1535])).

fof(f1974,plain,(
    ~ r1_xboole_0(sK2,sK5) ),
    inference(unit_resulting_resolution,[],[f1892,f1615])).
%------------------------------------------------------------------------------
