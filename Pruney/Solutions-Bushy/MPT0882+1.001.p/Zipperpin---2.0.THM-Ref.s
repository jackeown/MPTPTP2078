%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0882+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.deUfAjaTJn

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  252 ( 262 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t42_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) )
        = ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) ) ),
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

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_tarski @ ( k4_tarski @ X8 @ X9 ) @ ( k4_tarski @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) )
      = ( k1_tarski @ ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).


%------------------------------------------------------------------------------
