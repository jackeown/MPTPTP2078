%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D8jideuWaQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 154 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  491 (1111 expanded)
%              Number of equality atoms :   44 (  79 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( r2_hidden @ X68 @ X67 )
      | ~ ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('9',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( r2_hidden @ X66 @ X67 )
      | ~ ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X66: $i,X68: $i,X69: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X69 )
      | ~ ( r2_hidden @ X68 @ X69 )
      | ~ ( r2_hidden @ X66 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','21','22','23'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X65: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','45'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( r2_hidden @ X66 @ X67 )
      | ~ ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D8jideuWaQ
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 175 iterations in 0.076s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(t45_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.20/0.52       ( r2_hidden @ A @ B ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.20/0.52          ( r2_hidden @ A @ B ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.20/0.52  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.52        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('5', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.52  thf(t38_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.20/0.52         ((r2_hidden @ X68 @ X67)
% 0.20/0.52          | ~ (r1_tarski @ (k2_tarski @ X66 @ X68) @ X67))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.20/0.52         ((r2_hidden @ X66 @ X67)
% 0.20/0.52          | ~ (r1_tarski @ (k2_tarski @ X66 @ X68) @ X67))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X66 : $i, X68 : $i, X69 : $i]:
% 0.20/0.52         ((r1_tarski @ (k2_tarski @ X66 @ X68) @ X69)
% 0.20/0.52          | ~ (r2_hidden @ X68 @ X69)
% 0.20/0.52          | ~ (r2_hidden @ X66 @ X69))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.20/0.52          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X63 : $i, X64 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X63 : $i, X64 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf(t7_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('24', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '21', '22', '23'])).
% 0.20/0.52  thf(t95_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X14 @ X15)
% 0.20/0.52           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.20/0.52              (k2_xboole_0 @ X14 @ X15)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.52  thf(t91_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.20/0.52           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X14 @ X15)
% 0.20/0.52           = (k5_xboole_0 @ X14 @ 
% 0.20/0.52              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.52         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.52  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.52  thf(t92_xboole_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('30', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.20/0.52           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(t31_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.52  thf('34', plain, (![X65 : $i]: ((k3_tarski @ (k1_tarski @ X65)) = (X65))),
% 0.20/0.52      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.52  thf('35', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X63 : $i, X64 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X14 @ X15)
% 0.20/0.52           = (k5_xboole_0 @ X14 @ 
% 0.20/0.52              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.52  thf('40', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.52  thf('41', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.52  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '45'])).
% 0.20/0.52  thf(t17_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.52  thf('48', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.52      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.20/0.52         ((r2_hidden @ X66 @ X67)
% 0.20/0.52          | ~ (r1_tarski @ (k2_tarski @ X66 @ X68) @ X67))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.52  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
