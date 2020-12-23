%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0905+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g45SOpkeYp

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :  226 ( 236 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t65_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
        = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_mcart_1])).

thf('0',plain,(
    ( k4_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) )
      = ( k1_tarski @ ( k4_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 @ X15 )
      = ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X3 @ X2 )
      = ( k4_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t39_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','3','4','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).


%------------------------------------------------------------------------------
