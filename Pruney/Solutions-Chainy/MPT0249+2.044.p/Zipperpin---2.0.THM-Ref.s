%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bg1Udx22S0

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 245 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  405 (1905 expanded)
%              Number of equality atoms :   66 ( 408 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k1_tarski @ X26 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X31 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C_1 = o_0_0_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','38'])).

thf('40',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('43',plain,
    ( ( sk_C_1 = o_0_0_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('45',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['12','47'])).

thf('49',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bg1Udx22S0
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 501 iterations in 0.150s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.61  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.40/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.61  thf(t7_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.61  thf(t44_zfmisc_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.40/0.61          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.61        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.40/0.61             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.40/0.61  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(l3_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.40/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         (((X27) = (k1_tarski @ X26))
% 0.40/0.61          | ((X27) = (k1_xboole_0))
% 0.40/0.61          | ~ (r1_tarski @ X27 @ (k1_tarski @ X26)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.40/0.61  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.40/0.61  thf('3', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         (((X27) = (k1_tarski @ X26))
% 0.40/0.61          | ((X27) = (o_0_0_xboole_0))
% 0.40/0.61          | ~ (r1_tarski @ X27 @ (k1_tarski @ X26)))),
% 0.40/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.40/0.61          | ((X0) = (o_0_0_xboole_0))
% 0.40/0.61          | ((X0) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.61  thf('6', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.40/0.61          | ((X0) = (o_0_0_xboole_0))
% 0.40/0.61          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.40/0.61        | ((sk_B_1) = (o_0_0_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '7'])).
% 0.40/0.61  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('10', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.61  thf('11', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.61  thf('12', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.40/0.61  thf(t7_xboole_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.61  thf('14', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.40/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf('16', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.40/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf(d3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.40/0.61       ( ![D:$i]:
% 0.40/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.61           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.61          | (r2_hidden @ X0 @ X2)
% 0.40/0.61          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.40/0.61         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((X0) = (o_0_0_xboole_0))
% 0.40/0.61          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['17', '19'])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1) | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['16', '20'])).
% 0.40/0.61  thf('22', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('23', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.61  thf('24', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('25', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.40/0.61  thf('26', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('27', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.40/0.61  thf('28', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.40/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf(d1_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X14 @ X13)
% 0.40/0.61          | ((X14) = (X11))
% 0.40/0.61          | ((X13) != (k1_tarski @ X11)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X11 : $i, X14 : $i]:
% 0.40/0.61         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['28', '30'])).
% 0.40/0.61  thf('32', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['25', '31'])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.40/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.40/0.61  thf('35', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('36', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.40/0.61  thf(t38_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.40/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.40/0.61         ((r1_tarski @ (k2_tarski @ X31 @ X33) @ X34)
% 0.40/0.61          | ~ (r2_hidden @ X33 @ X34)
% 0.40/0.61          | ~ (r2_hidden @ X31 @ X34))),
% 0.40/0.61      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.40/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      ((((sk_C_1) = (o_0_0_xboole_0))
% 0.40/0.61        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C_1) @ sk_A) @ sk_C_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['15', '38'])).
% 0.40/0.61  thf('40', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['25', '31'])).
% 0.40/0.61  thf(t69_enumset1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.40/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.61  thf('42', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.40/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      ((((sk_C_1) = (o_0_0_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.40/0.61  thf('44', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('45', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.40/0.61  thf(t12_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      (![X7 : $i, X8 : $i]:
% 0.40/0.61         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.61  thf('47', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.61  thf('48', plain, (((sk_B_1) = (sk_C_1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['12', '47'])).
% 0.40/0.61  thf('49', plain, (((sk_B_1) != (sk_C_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('50', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
