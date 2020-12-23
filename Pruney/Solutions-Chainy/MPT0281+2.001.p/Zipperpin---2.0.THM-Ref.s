%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ptuu2h8nkp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:46 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 102 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  506 ( 779 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t82_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
        = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
     => ( r3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
          = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
       => ( r3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t82_zfmisc_1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X35 )
      | ( X35
       != ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    = ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( r1_tarski @ X36 @ X34 )
      | ( X35
       != ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ X36 @ X34 )
      | ~ ( r2_hidden @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ X36 @ X34 )
      | ~ ( r2_hidden @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r3_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r3_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ptuu2h8nkp
% 0.11/0.30  % Computer   : n025.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:11:36 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running portfolio for 600 s
% 0.11/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.16/0.31  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 392 iterations in 0.321s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.74  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.52/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(t82_zfmisc_1, conjecture,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.52/0.74         ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.52/0.74       ( r3_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i,B:$i]:
% 0.52/0.74        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.52/0.74            ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.52/0.74          ( r3_xboole_0 @ A @ B ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t82_zfmisc_1])).
% 0.52/0.74  thf('0', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(d10_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.74  thf('1', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.52/0.74      inference('simplify', [status(thm)], ['1'])).
% 0.52/0.74  thf(d1_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.52/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (~ (r1_tarski @ X33 @ X34)
% 0.52/0.74          | (r2_hidden @ X33 @ X35)
% 0.52/0.74          | ((X35) != (k1_zfmisc_1 @ X34)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i]:
% 0.52/0.74         ((r2_hidden @ X33 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X33 @ X34))),
% 0.52/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.74  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['2', '4'])).
% 0.52/0.74  thf('6', plain,
% 0.52/0.74      (((k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.52/0.74         = (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['2', '4'])).
% 0.52/0.74  thf(d5_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.52/0.74       ( ![D:$i]:
% 0.52/0.74         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.74           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.74          | (r2_hidden @ X0 @ X2)
% 0.52/0.74          | (r2_hidden @ X0 @ X3)
% 0.52/0.74          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.74  thf('9', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.52/0.74          | (r2_hidden @ X0 @ X2)
% 0.52/0.74          | ~ (r2_hidden @ X0 @ X1))),
% 0.52/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.74  thf('10', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         ((r2_hidden @ X0 @ X1)
% 0.52/0.74          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.74  thf('11', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.52/0.74          | (r2_hidden @ X0 @ X2)
% 0.52/0.74          | ~ (r2_hidden @ X0 @ X1))),
% 0.52/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((r2_hidden @ X1 @ X0)
% 0.52/0.74          | (r2_hidden @ X1 @ X2)
% 0.52/0.74          | (r2_hidden @ X1 @ 
% 0.52/0.74             (k4_xboole_0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X1) @ X0) @ X2)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.74  thf(t41_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.52/0.74  thf('13', plain,
% 0.52/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.52/0.74           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.74  thf('14', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((r2_hidden @ X1 @ X0)
% 0.52/0.74          | (r2_hidden @ X1 @ X2)
% 0.52/0.74          | (r2_hidden @ X1 @ 
% 0.52/0.74             (k4_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k2_xboole_0 @ X0 @ X2))))),
% 0.52/0.74      inference('demod', [status(thm)], ['12', '13'])).
% 0.52/0.74  thf('15', plain,
% 0.52/0.74      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X4 @ X3)
% 0.52/0.74          | ~ (r2_hidden @ X4 @ X2)
% 0.52/0.74          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.74  thf('16', plain,
% 0.52/0.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.74          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['15'])).
% 0.52/0.74  thf('17', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((r2_hidden @ X2 @ X0)
% 0.52/0.74          | (r2_hidden @ X2 @ X1)
% 0.52/0.74          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['14', '16'])).
% 0.52/0.74  thf('18', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))
% 0.52/0.74          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['6', '17'])).
% 0.52/0.74  thf('19', plain,
% 0.52/0.74      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))
% 0.52/0.74        | (r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['5', '18'])).
% 0.52/0.74  thf('20', plain,
% 0.52/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X36 @ X35)
% 0.52/0.74          | (r1_tarski @ X36 @ X34)
% 0.52/0.74          | ((X35) != (k1_zfmisc_1 @ X34)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.74  thf('21', plain,
% 0.52/0.74      (![X34 : $i, X36 : $i]:
% 0.52/0.74         ((r1_tarski @ X36 @ X34) | ~ (r2_hidden @ X36 @ (k1_zfmisc_1 @ X34)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['20'])).
% 0.52/0.74  thf('22', plain,
% 0.52/0.74      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['19', '21'])).
% 0.52/0.74  thf('23', plain,
% 0.52/0.74      (![X34 : $i, X36 : $i]:
% 0.52/0.74         ((r1_tarski @ X36 @ X34) | ~ (r2_hidden @ X36 @ (k1_zfmisc_1 @ X34)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['20'])).
% 0.52/0.74  thf('24', plain,
% 0.52/0.74      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.52/0.74        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.74  thf(commutativity_k2_tarski, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.52/0.74  thf('25', plain,
% 0.52/0.74      (![X17 : $i, X18 : $i]:
% 0.52/0.74         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.52/0.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.52/0.74  thf(l51_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf('26', plain,
% 0.52/0.74      (![X38 : $i, X39 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('27', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['25', '26'])).
% 0.52/0.74  thf('28', plain,
% 0.52/0.74      (![X38 : $i, X39 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('29', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.52/0.74  thf(t7_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf('30', plain,
% 0.52/0.74      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.74  thf('31', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['29', '30'])).
% 0.52/0.74  thf('32', plain,
% 0.52/0.74      (![X6 : $i, X8 : $i]:
% 0.52/0.74         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('33', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.52/0.74          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.74  thf('34', plain,
% 0.52/0.74      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.52/0.74        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_B)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['24', '33'])).
% 0.52/0.74  thf('35', plain,
% 0.52/0.74      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.74  thf('36', plain,
% 0.52/0.74      (![X6 : $i, X8 : $i]:
% 0.52/0.74         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('37', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.74          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.52/0.74  thf('38', plain,
% 0.52/0.74      ((((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))
% 0.52/0.74        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['34', '37'])).
% 0.52/0.74  thf('39', plain,
% 0.52/0.74      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.74  thf(d9_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.52/0.74       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.74  thf('40', plain,
% 0.52/0.74      (![X10 : $i, X11 : $i]:
% 0.52/0.74         ((r3_xboole_0 @ X10 @ X11) | ~ (r1_tarski @ X10 @ X11))),
% 0.52/0.74      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.52/0.74  thf('41', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.74  thf('42', plain,
% 0.52/0.74      (((r3_xboole_0 @ sk_A @ sk_B) | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['38', '41'])).
% 0.52/0.74  thf('43', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('44', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.52/0.74      inference('clc', [status(thm)], ['42', '43'])).
% 0.52/0.74  thf('45', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.52/0.74  thf('46', plain,
% 0.52/0.74      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.74  thf('47', plain,
% 0.52/0.74      (![X10 : $i, X11 : $i]:
% 0.52/0.74         ((r3_xboole_0 @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.52/0.74  thf('48', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)),
% 0.52/0.74      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.74  thf('49', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)),
% 0.52/0.74      inference('sup+', [status(thm)], ['45', '48'])).
% 0.52/0.74  thf('50', plain, ((r3_xboole_0 @ sk_A @ sk_B)),
% 0.52/0.74      inference('sup+', [status(thm)], ['44', '49'])).
% 0.52/0.74  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
