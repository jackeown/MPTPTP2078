%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0907+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   26 (  49 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 129 expanded)
%              Number of equality atoms :   29 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2790,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2708,f1959])).

fof(f1959,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2708,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f2304,f2699])).

fof(f2699,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(global_subsumption,[],[f1699,f2695,f2696])).

fof(f2696,plain,
    ( sK0 != k2_mcart_1(sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f2303,f1723])).

fof(f1723,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1373])).

fof(f1373,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f2303,plain,(
    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f1698,f1955])).

fof(f1955,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1504])).

fof(f1504,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f1698,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f1547])).

fof(f1547,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1385,f1546])).

fof(f1546,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1385,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1375])).

fof(f1375,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f1374])).

fof(f1374,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f2695,plain,
    ( sK0 != k1_mcart_1(sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f2303,f1722])).

fof(f1722,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_mcart_1(X2) != X2
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1699,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1547])).

fof(f2304,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f1698,f1987])).

fof(f1987,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1522])).

fof(f1522,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
%------------------------------------------------------------------------------
