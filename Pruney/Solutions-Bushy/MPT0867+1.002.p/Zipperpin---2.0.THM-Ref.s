%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0867+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IKWtF6ycrq

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:37 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :  323 ( 440 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t25_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_mcart_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_enumset1 @ ( k4_tarski @ sk_A @ sk_C ) @ ( k4_tarski @ sk_A @ sk_D ) @ ( k4_tarski @ sk_B @ sk_C ) @ ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_tarski @ ( k4_tarski @ X6 @ X7 ) @ ( k4_tarski @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_tarski @ ( k4_tarski @ X6 @ X7 ) @ ( k4_tarski @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X2 @ X0 ) @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X5 @ X3 ) @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X4 @ X3 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t132_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X4 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X4 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X2 ) @ X0 )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','5','8','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).


%------------------------------------------------------------------------------
