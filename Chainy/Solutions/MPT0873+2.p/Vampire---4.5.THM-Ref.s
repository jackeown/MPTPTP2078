%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0873+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   24 (  90 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 266 expanded)
%              Number of equality atoms :   60 ( 265 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2864,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2796,f2859])).

fof(f2859,plain,(
    sK35 != sK39 ),
    inference(subsumption_resolution,[],[f2725,f2797])).

fof(f2797,plain,(
    sK36 = sK40 ),
    inference(unit_resulting_resolution,[],[f2658,f1899])).

fof(f1899,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f1340,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f391])).

fof(f391,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f2658,plain,(
    k4_tarski(sK35,sK36) = k4_tarski(sK39,sK40) ),
    inference(unit_resulting_resolution,[],[f2524,f1898])).

fof(f1898,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f2524,plain,(
    k4_tarski(k4_tarski(sK35,sK36),sK37) = k4_tarski(k4_tarski(sK39,sK40),sK41) ),
    inference(unit_resulting_resolution,[],[f2333,f1898])).

fof(f2333,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK35,sK36),sK37),sK38) = k4_tarski(k4_tarski(k4_tarski(sK39,sK40),sK41),sK42) ),
    inference(definition_unfolding,[],[f1858,f1860,f1860])).

fof(f1860,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1315])).

fof(f1315,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f1858,plain,(
    k4_mcart_1(sK35,sK36,sK37,sK38) = k4_mcart_1(sK39,sK40,sK41,sK42) ),
    inference(cnf_transformation,[],[f1619])).

fof(f1619,plain,
    ( ( sK38 != sK42
      | sK37 != sK41
      | sK36 != sK40
      | sK35 != sK39 )
    & k4_mcart_1(sK35,sK36,sK37,sK38) = k4_mcart_1(sK39,sK40,sK41,sK42) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37,sK38,sK39,sK40,sK41,sK42])],[f1328,f1618])).

fof(f1618,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK38 != sK42
        | sK37 != sK41
        | sK36 != sK40
        | sK35 != sK39 )
      & k4_mcart_1(sK35,sK36,sK37,sK38) = k4_mcart_1(sK39,sK40,sK41,sK42) ) ),
    introduced(choice_axiom,[])).

fof(f1328,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1318])).

fof(f1318,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f1317])).

fof(f1317,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f2725,plain,
    ( sK36 != sK40
    | sK35 != sK39 ),
    inference(subsumption_resolution,[],[f2591,f2659])).

fof(f2659,plain,(
    sK37 = sK41 ),
    inference(unit_resulting_resolution,[],[f2524,f1899])).

fof(f2591,plain,
    ( sK37 != sK41
    | sK36 != sK40
    | sK35 != sK39 ),
    inference(subsumption_resolution,[],[f1859,f2525])).

fof(f2525,plain,(
    sK38 = sK42 ),
    inference(unit_resulting_resolution,[],[f2333,f1899])).

fof(f1859,plain,
    ( sK38 != sK42
    | sK37 != sK41
    | sK36 != sK40
    | sK35 != sK39 ),
    inference(cnf_transformation,[],[f1619])).

fof(f2796,plain,(
    sK35 = sK39 ),
    inference(unit_resulting_resolution,[],[f2658,f1898])).
%------------------------------------------------------------------------------
