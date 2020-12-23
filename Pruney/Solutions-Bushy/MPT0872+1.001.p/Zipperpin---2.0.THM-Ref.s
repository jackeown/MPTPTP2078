%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0872+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.djEHRYeTkS

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  127 ( 137 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t32_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t32_mcart_1])).

thf('0',plain,(
    ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k3_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).


%------------------------------------------------------------------------------
