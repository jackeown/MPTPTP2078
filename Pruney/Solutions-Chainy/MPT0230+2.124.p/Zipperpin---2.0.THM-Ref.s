%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZiVaCy9wqZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  378 ( 574 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X27 @ X29 ) @ X30 )
        = ( k1_tarski @ X27 ) )
      | ( X27 != X29 )
      | ( r2_hidden @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X29 ) @ X30 )
        = ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
        = ( k1_tarski @ X29 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ( X15 = X14 )
      | ( X15 = X11 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( X15 = X11 )
      | ( X15 = X14 )
      | ~ ( r2_hidden @ X15 @ ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
    | ( sk_A = sk_B_1 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZiVaCy9wqZ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 62 iterations in 0.046s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('0', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(d2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) != (X11))
% 0.20/0.51          | (r2_hidden @ X12 @ X13)
% 0.20/0.51          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.20/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.51  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.51  thf(t25_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.51          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.51             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t28_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.20/0.51         = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(t100_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.51           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.20/0.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.51           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.51  thf(t1_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.51       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | ~ (r2_hidden @ X3 @ X5)
% 0.20/0.51          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.51          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.51          | ~ (r2_hidden @ X2 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ 
% 0.20/0.51             (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ 
% 0.20/0.51               (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.20/0.51         = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ 
% 0.20/0.51             (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ 
% 0.20/0.51               (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.51  thf(l38_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.20/0.51         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ (k2_tarski @ X27 @ X29) @ X30) = (k1_tarski @ X27))
% 0.20/0.51          | ((X27) != (X29))
% 0.20/0.51          | (r2_hidden @ X27 @ X30))),
% 0.20/0.51      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i]:
% 0.20/0.51         ((r2_hidden @ X29 @ X30)
% 0.20/0.51          | ((k4_xboole_0 @ (k2_tarski @ X29 @ X29) @ X30) = (k1_tarski @ X29)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i]:
% 0.20/0.51         ((r2_hidden @ X29 @ X30)
% 0.20/0.51          | ((k4_xboole_0 @ (k1_tarski @ X29) @ X30) = (k1_tarski @ X29)))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.20/0.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A)
% 0.20/0.51          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.20/0.51        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X15 @ X13)
% 0.20/0.51          | ((X15) = (X14))
% 0.20/0.51          | ((X15) = (X11))
% 0.20/0.51          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (((X15) = (X11))
% 0.20/0.51          | ((X15) = (X14))
% 0.20/0.51          | ~ (r2_hidden @ X15 @ (k2_tarski @ X14 @ X11)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A)
% 0.20/0.51          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.20/0.51        | ((sk_A) = (sk_B_1))
% 0.20/0.51        | ((sk_A) = (sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.51  thf('25', plain, (((sk_A) != (sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((k1_tarski @ sk_A)
% 0.20/0.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['24', '25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '27'])).
% 0.20/0.51  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.51  thf('30', plain, ($false), inference('sup-', [status(thm)], ['3', '29'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
