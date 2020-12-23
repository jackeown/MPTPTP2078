%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YjVLX76BsE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 125 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  461 ( 990 expanded)
%              Number of equality atoms :   53 ( 143 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('2',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('4',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('6',plain,(
    r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('11',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','19'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('22',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','18'])).

thf('27',plain,
    ( ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['27','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','36'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('42',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['45','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YjVLX76BsE
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 144 iterations in 0.057s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(t66_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.53             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d6_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k5_xboole_0 @ A @ B ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53         = (k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.20/0.53            k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(t1_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('3', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t36_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.20/0.53        (k1_tarski @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X9 : $i, X11 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.20/0.53         (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.53         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53            (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t4_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf(t12_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.53  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ 
% 0.20/0.53         (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '19'])).
% 0.20/0.53  thf(t65_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X37 : $i, X38 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 0.20/0.53          | (r2_hidden @ X38 @ X37))),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((k1_xboole_0) = (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.53        | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) != (k1_xboole_0))
% 0.20/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12', '18'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (k1_xboole_0))
% 0.20/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X6 : $i, X8 : $i]:
% 0.20/0.53         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['27', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['22', '36'])).
% 0.20/0.53  thf(t1_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.53       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X4)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X37 : $i, X38 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 0.20/0.53          | (r2_hidden @ X38 @ X37))),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.53  thf('42', plain, ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '44'])).
% 0.20/0.53  thf(d1_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.53         (((X26) != (X25))
% 0.20/0.53          | (r2_hidden @ X26 @ X27)
% 0.20/0.53          | ((X27) != (k1_tarski @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('47', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.20/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.53  thf('48', plain, ($false), inference('demod', [status(thm)], ['45', '47'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
