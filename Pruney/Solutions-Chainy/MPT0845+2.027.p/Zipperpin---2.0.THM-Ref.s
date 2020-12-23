%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CAHFvO0dp6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:37 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 152 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 (1405 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('4',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r1_xboole_0 @ X46 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ~ ( r1_xboole_0 @ ( sk_D @ X1 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( r2_hidden @ ( sk_C_1 @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r1_xboole_0 @ X46 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X43 @ X42 )
      | ~ ( r2_hidden @ X43 @ ( sk_C_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('23',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r1_xboole_0 @ X46 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ~ ( r1_xboole_0 @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A )
      | ( sk_A
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r1_xboole_0 @ X46 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1 = sk_A ) ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( r2_hidden @ ( sk_C_1 @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_A )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CAHFvO0dp6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 116 iterations in 0.100s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.57  thf('0', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.38/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.57  thf(d4_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.57         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.38/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.38/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.57  thf(t12_setfam_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X44 : $i, X45 : $i]:
% 0.38/0.57         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.57         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.38/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.38/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(t1_mcart_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.57          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.57             ( ![B:$i]:
% 0.38/0.57               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X46 : $i]: (~ (r2_hidden @ X46 @ sk_A) | ~ (r1_xboole_0 @ X46 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1)
% 0.38/0.57          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))
% 0.38/0.57          | ~ (r1_xboole_0 @ (sk_D @ X1 @ sk_A @ X0) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.57  thf(t3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.38/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.57  thf(t7_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ~( ( r2_hidden @ A @ B ) & 
% 0.38/0.57          ( ![C:$i]:
% 0.38/0.57            ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.57                 ( ![D:$i]:
% 0.38/0.57                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X41 : $i, X42 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X41 @ X42) | (r2_hidden @ (sk_C_1 @ X42) @ X42))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X46 : $i]: (~ (r2_hidden @ X46 @ sk_A) | ~ (r1_xboole_0 @ X46 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X41 @ X42)
% 0.38/0.57          | ~ (r2_hidden @ X43 @ X42)
% 0.38/0.57          | ~ (r2_hidden @ X43 @ (sk_C_1 @ X42)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.57      inference('condensation', [status(thm)], ['13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.38/0.57          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['12', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.38/0.57          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '15'])).
% 0.38/0.57  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.38/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.57  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['10', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1)
% 0.38/0.57          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['5', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.57         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.38/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.38/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.38/0.57          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.38/0.57      inference('eq_fact', [status(thm)], ['21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X46 : $i]: (~ (r2_hidden @ X46 @ sk_A) | ~ (r1_xboole_0 @ X46 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((sk_A) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))
% 0.38/0.57          | ~ (r1_xboole_0 @ (sk_D @ sk_A @ sk_A @ X0) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)
% 0.38/0.57          | ((sk_A) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X46 : $i]: (~ (r2_hidden @ X46 @ sk_A) | ~ (r1_xboole_0 @ X46 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((sk_A) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))
% 0.38/0.57          | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.38/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i]: ((sk_A) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1) | ((X1) = (sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['19', '29'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X41 : $i, X42 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X41 @ X42) | (r2_hidden @ (sk_C_1 @ X42) @ X42))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (sk_A)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (sk_A)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X11 @ X9)
% 0.38/0.57          | ~ (r2_hidden @ X11 @ X12)
% 0.38/0.57          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (sk_A))
% 0.38/0.57          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.38/0.57          | ~ (r2_hidden @ (sk_C_1 @ X0) @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((X0) = (sk_A)) | ~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['32', '35'])).
% 0.38/0.57  thf('37', plain, (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.57  thf('38', plain, (((k1_xboole_0) = (sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '37'])).
% 0.38/0.57  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('40', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
