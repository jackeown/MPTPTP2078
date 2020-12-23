%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCcuuDNPk6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 123 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  416 ( 903 expanded)
%              Number of equality atoms :   50 ( 131 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) )
        = X32 )
      | ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

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

thf('1',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf('20',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','13'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['22','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','31'])).

thf('33',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) )
        = X32 )
      | ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('40',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['37','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCcuuDNPk6
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 156 iterations in 0.051s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(t65_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i]:
% 0.22/0.53         (((k4_xboole_0 @ X32 @ (k1_tarski @ X33)) = (X32))
% 0.22/0.53          | (r2_hidden @ X33 @ X32))),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.53  thf(t66_zfmisc_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.22/0.53          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.22/0.53             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d6_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k5_xboole_0 @ A @ B ) =
% 0.22/0.53       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i]:
% 0.22/0.53         ((k5_xboole_0 @ X6 @ X7)
% 0.22/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.53         = (k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.22/0.53            k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf(t3_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.53  thf('4', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i]:
% 0.22/0.53         ((k5_xboole_0 @ X6 @ X7)
% 0.22/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.22/0.53           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf(t2_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.53  thf(t100_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X14 @ X15)
% 0.22/0.53           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.53  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf(t4_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.53  thf('13', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['6', '11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.53         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['3', '13'])).
% 0.22/0.53  thf(t36_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.22/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.53  thf(l32_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X11 : $i, X13 : $i]:
% 0.22/0.53         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.22/0.53          | ~ (r1_tarski @ X11 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.22/0.53         (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.22/0.53        | (r2_hidden @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['0', '18'])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.53         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['3', '13'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i]:
% 0.22/0.53         ((r1_tarski @ X11 @ X12)
% 0.22/0.53          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) != (k1_xboole_0))
% 0.22/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i]:
% 0.22/0.53         ((r1_tarski @ X11 @ X12)
% 0.22/0.53          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.53        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.53  thf(d10_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X8 : $i, X10 : $i]:
% 0.22/0.53         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.22/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.53        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.53  thf('29', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('30', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) != (k1_xboole_0))),
% 0.22/0.53      inference('clc', [status(thm)], ['22', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      ((r2_hidden @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['19', '31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.53         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['3', '13'])).
% 0.22/0.53  thf(d5_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.53       ( ![D:$i]:
% 0.22/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.53          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['33', '35'])).
% 0.22/0.53  thf('37', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['32', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i]:
% 0.22/0.53         (((k4_xboole_0 @ X32 @ (k1_tarski @ X33)) = (X32))
% 0.22/0.53          | (r2_hidden @ X33 @ X32))),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.53  thf('40', plain, ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.53  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('42', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.22/0.53  thf('43', plain, ($false), inference('demod', [status(thm)], ['37', '42'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
