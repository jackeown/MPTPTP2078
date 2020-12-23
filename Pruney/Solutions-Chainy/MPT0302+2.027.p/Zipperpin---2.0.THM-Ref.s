%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6xTrbldsCQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:09 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 125 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  440 (1036 expanded)
%              Number of equality atoms :   25 (  95 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_2 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('23',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_xboole_0 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('42',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6xTrbldsCQ
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 20:48:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 171 iterations in 0.125s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.61  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.37/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(d3_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X1 : $i, X3 : $i]:
% 0.37/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf(t2_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.61       ( ( A ) = ( B ) ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         (((X8) = (X7))
% 0.37/0.61          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 0.37/0.61          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.61  thf('2', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.37/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.61  thf(l24_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i]:
% 0.37/0.61         (~ (r1_xboole_0 @ (k1_tarski @ X12) @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.37/0.61      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.37/0.61  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.37/0.61          | ((k1_xboole_0) = (X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.61  thf(l54_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.37/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.37/0.61         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 0.37/0.61          | ~ (r2_hidden @ X16 @ X18)
% 0.37/0.61          | ~ (r2_hidden @ X14 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (((k1_xboole_0) = (X0))
% 0.37/0.61          | ~ (r2_hidden @ X2 @ X1)
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.61             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((r1_tarski @ X0 @ X1)
% 0.37/0.61          | (r2_hidden @ 
% 0.37/0.61             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 0.37/0.61             (k2_zfmisc_1 @ X0 @ X2))
% 0.37/0.61          | ((k1_xboole_0) = (X2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '7'])).
% 0.37/0.61  thf(t114_zfmisc_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.37/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.61         ( ( A ) = ( B ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i]:
% 0.37/0.61        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.37/0.61          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.61            ( ( A ) = ( B ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         ((r2_hidden @ X14 @ X15)
% 0.37/0.61          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.37/0.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.37/0.61          | (r2_hidden @ X1 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k1_xboole_0) = (sk_B))
% 0.37/0.61          | (r1_tarski @ sk_A @ X0)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.61  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X1 : $i, X3 : $i]:
% 0.37/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('16', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf('17', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.61  thf(d8_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.61       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X4 : $i, X6 : $i]:
% 0.37/0.61         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.61  thf('19', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('20', plain, (((sk_A) != (sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('21', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf(t6_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.37/0.61          ( ![C:$i]:
% 0.37/0.61            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         (~ (r2_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_2 @ X10 @ X9) @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.37/0.61  thf('23', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.37/0.61          | ((k1_xboole_0) = (X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X1 : $i, X3 : $i]:
% 0.37/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.37/0.61         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 0.37/0.61          | ~ (r2_hidden @ X16 @ X18)
% 0.37/0.61          | ~ (r2_hidden @ X14 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.61         ((r1_tarski @ X0 @ X1)
% 0.37/0.61          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.37/0.61             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (((k1_xboole_0) = (X0))
% 0.37/0.61          | (r2_hidden @ 
% 0.37/0.61             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.37/0.61             (k2_zfmisc_1 @ X0 @ X1))
% 0.37/0.61          | (r1_tarski @ X1 @ X2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['24', '27'])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         ((r2_hidden @ X16 @ X17)
% 0.37/0.61          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.37/0.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.37/0.61          | (r2_hidden @ X0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ sk_B @ X0)
% 0.37/0.61          | ((k1_xboole_0) = (sk_A))
% 0.37/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['28', '31'])).
% 0.37/0.61  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X1 : $i, X3 : $i]:
% 0.37/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('36', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.61          | (r2_hidden @ X0 @ X2)
% 0.37/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf('40', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.37/0.61      inference('sup-', [status(thm)], ['23', '39'])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         (~ (r2_xboole_0 @ X9 @ X10) | ~ (r2_hidden @ (sk_C_2 @ X10 @ X9) @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.37/0.61  thf('42', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('44', plain, ($false), inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
