%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.91x4bjuhnn

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 124 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  469 (1022 expanded)
%              Number of equality atoms :   84 ( 215 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X27
        = ( k2_tarski @ X25 @ X26 ) )
      | ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27
        = ( k1_tarski @ X25 ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X27
        = ( k2_tarski @ X25 @ X26 ) )
      | ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27
        = ( k1_tarski @ X25 ) )
      | ( X27 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( sk_C_1 = o_0_0_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('34',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['17','44'])).

thf('46',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.91x4bjuhnn
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 408 iterations in 0.120s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(t7_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.57  thf(t44_zfmisc_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.39/0.57          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.39/0.57             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.39/0.57  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t69_enumset1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.57  thf('2', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.39/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.57  thf(l45_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.39/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.39/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.57         (((X27) = (k2_tarski @ X25 @ X26))
% 0.39/0.57          | ((X27) = (k1_tarski @ X26))
% 0.39/0.57          | ((X27) = (k1_tarski @ X25))
% 0.39/0.57          | ((X27) = (k1_xboole_0))
% 0.39/0.57          | ~ (r1_tarski @ X27 @ (k2_tarski @ X25 @ X26)))),
% 0.39/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.39/0.57  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.39/0.57  thf('4', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.57         (((X27) = (k2_tarski @ X25 @ X26))
% 0.39/0.57          | ((X27) = (k1_tarski @ X26))
% 0.39/0.57          | ((X27) = (k1_tarski @ X25))
% 0.39/0.57          | ((X27) = (o_0_0_xboole_0))
% 0.39/0.57          | ~ (r1_tarski @ X27 @ (k2_tarski @ X25 @ X26)))),
% 0.39/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X1) = (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '5'])).
% 0.39/0.57  thf('7', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.39/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X1) = (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (k1_tarski @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((X1) = (k1_tarski @ X0))
% 0.39/0.57          | ((X1) = (o_0_0_xboole_0))
% 0.39/0.57          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.39/0.57          | ((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X0) = (k1_tarski @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '9'])).
% 0.39/0.57  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.39/0.57          | ((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.39/0.57        | ((sk_B_1) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '12'])).
% 0.39/0.57  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('16', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['13', '16'])).
% 0.39/0.57  thf(t7_xboole_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.57  thf('19', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf(d3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.57           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | (r2_hidden @ X0 @ X2)
% 0.39/0.57          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '22'])).
% 0.39/0.57  thf('24', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d1_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X14 @ X13)
% 0.39/0.57          | ((X14) = (X11))
% 0.39/0.57          | ((X13) != (k1_tarski @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X11 : $i, X14 : $i]:
% 0.39/0.57         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.39/0.57          | ((X0) = (sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      ((((sk_C_1) = (o_0_0_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '27'])).
% 0.39/0.57  thf('29', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('30', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('31', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.57  thf('32', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf(l1_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X22 : $i, X24 : $i]:
% 0.39/0.57         ((r1_tarski @ (k1_tarski @ X22) @ X24) | ~ (r2_hidden @ X22 @ X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf(t12_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))
% 0.39/0.57        | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['32', '37'])).
% 0.39/0.57  thf('39', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((((k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_C_1) = (sk_C_1))
% 0.39/0.57        | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (((k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_C_1) = (sk_C_1))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['13', '16'])).
% 0.39/0.57  thf('44', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain, (((sk_B_1) = (sk_C_1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['17', '44'])).
% 0.39/0.57  thf('46', plain, (((sk_B_1) != (sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('47', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
