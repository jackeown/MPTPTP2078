%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J2xYEBN3Ql

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:50 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 176 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  398 (1150 expanded)
%              Number of equality atoms :   42 ( 103 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('8',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X18 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('24',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t105_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_xboole_0 @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( r2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X18 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_xboole_0 @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( r2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','29'])).

thf('39',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','29'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('43',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('45',plain,(
    ! [X21: $i,X24: $i] :
      ( r2_hidden @ X21 @ ( k2_tarski @ X24 @ X21 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['41','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J2xYEBN3Ql
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:53:08 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 153 iterations in 0.071s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.34/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(t49_zfmisc_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i]:
% 0.34/0.53        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t96_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X19 : $i, X20 : $i]:
% 0.34/0.53         (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ (k5_xboole_0 @ X19 @ X20))),
% 0.34/0.53      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.34/0.53  thf(t107_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.34/0.53       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.34/0.53         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.53         ((r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.34/0.53          | ~ (r1_tarski @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ k1_xboole_0)),
% 0.34/0.53      inference('sup+', [status(thm)], ['0', '3'])).
% 0.34/0.53  thf(t3_xboole_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X15 : $i]:
% 0.34/0.53         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.53  thf(l33_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.34/0.53       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X30 : $i, X31 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X30 @ X31)
% 0.34/0.53          | ((k4_xboole_0 @ (k1_tarski @ X30) @ X31) != (k1_tarski @ X30)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      ((((k1_xboole_0) != (k1_tarski @ sk_A)) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.53  thf(t61_xboole_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X18 : $i]:
% 0.34/0.53         ((r2_xboole_0 @ k1_xboole_0 @ X18) | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.34/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X19 : $i, X20 : $i]:
% 0.34/0.53         (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ (k5_xboole_0 @ X19 @ X20))),
% 0.34/0.53      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.53         ((r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.34/0.53          | ~ (r1_tarski @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)),
% 0.34/0.53      inference('sup+', [status(thm)], ['10', '15'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X15 : $i]:
% 0.34/0.53         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf(t39_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X13 : $i, X14 : $i]:
% 0.34/0.53         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.34/0.53           = (k2_xboole_0 @ X13 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.34/0.53         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.34/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) @ 
% 0.34/0.53        k1_xboole_0)),
% 0.34/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (![X15 : $i]:
% 0.34/0.53         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.34/0.53  thf(t105_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.34/0.53          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i]:
% 0.34/0.53         (~ (r2_xboole_0 @ X4 @ X5)
% 0.34/0.53          | ((k4_xboole_0 @ X5 @ X4) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.53        | ~ (r2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.34/0.53  thf('29', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.34/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.34/0.53  thf('30', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['9', '29'])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.34/0.53      inference('demod', [status(thm)], ['8', '30'])).
% 0.34/0.53  thf('32', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.34/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (![X18 : $i]:
% 0.34/0.53         ((r2_xboole_0 @ k1_xboole_0 @ X18) | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i]:
% 0.34/0.53         (~ (r2_xboole_0 @ X4 @ X5)
% 0.34/0.53          | ((k4_xboole_0 @ X5 @ X4) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.53        | ~ (r2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf('37', plain, (~ (r2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.34/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.34/0.53  thf('38', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['9', '29'])).
% 0.34/0.53  thf('39', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.34/0.53  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['33', '39'])).
% 0.34/0.53  thf('41', plain, (~ (r2_hidden @ sk_A @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['32', '40'])).
% 0.34/0.53  thf('42', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['9', '29'])).
% 0.34/0.53  thf(t69_enumset1, axiom,
% 0.34/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.34/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.53  thf(d2_tarski, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.34/0.53       ( ![D:$i]:
% 0.34/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.53         (((X22) != (X21))
% 0.34/0.53          | (r2_hidden @ X22 @ X23)
% 0.34/0.53          | ((X23) != (k2_tarski @ X24 @ X21)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      (![X21 : $i, X24 : $i]: (r2_hidden @ X21 @ (k2_tarski @ X24 @ X21))),
% 0.34/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.53  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['43', '45'])).
% 0.34/0.53  thf('47', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.34/0.53      inference('sup+', [status(thm)], ['42', '46'])).
% 0.34/0.53  thf('48', plain, ($false), inference('demod', [status(thm)], ['41', '47'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
