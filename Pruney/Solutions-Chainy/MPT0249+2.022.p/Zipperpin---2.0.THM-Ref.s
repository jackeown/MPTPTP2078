%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UvzJpRHKY4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:41 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   57 (  97 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  338 ( 760 expanded)
%              Number of equality atoms :   54 ( 143 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','16','17'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['18','24'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('29',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UvzJpRHKY4
% 0.15/0.38  % Computer   : n022.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 11:39:11 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.53  % Solved by: fo/fo7.sh
% 0.25/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.53  % done 60 iterations in 0.033s
% 0.25/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.53  % SZS output start Refutation
% 0.25/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.25/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.53  thf(t44_zfmisc_1, conjecture,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.25/0.53          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.25/0.53          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.25/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.25/0.53             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.25/0.53             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.25/0.53    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.25/0.53  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf(t7_xboole_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.25/0.53  thf('2', plain,
% 0.25/0.53      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.25/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.25/0.53  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.25/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.25/0.53  thf(l3_zfmisc_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.25/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.25/0.53  thf('4', plain,
% 0.25/0.53      (![X42 : $i, X43 : $i]:
% 0.25/0.53         (((X43) = (k1_tarski @ X42))
% 0.25/0.53          | ((X43) = (k1_xboole_0))
% 0.25/0.53          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 0.25/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.25/0.53  thf('5', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.53  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('7', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.25/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.25/0.53  thf('8', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.25/0.53      inference('demod', [status(thm)], ['0', '7'])).
% 0.25/0.53  thf(t95_xboole_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( k3_xboole_0 @ A @ B ) =
% 0.25/0.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.25/0.53  thf('9', plain,
% 0.25/0.53      (![X12 : $i, X13 : $i]:
% 0.25/0.53         ((k3_xboole_0 @ X12 @ X13)
% 0.25/0.53           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.25/0.53              (k2_xboole_0 @ X12 @ X13)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.25/0.53  thf(t91_xboole_1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.25/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.25/0.53  thf('10', plain,
% 0.25/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.25/0.53           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.25/0.53  thf('11', plain,
% 0.25/0.53      (![X12 : $i, X13 : $i]:
% 0.25/0.53         ((k3_xboole_0 @ X12 @ X13)
% 0.25/0.53           = (k5_xboole_0 @ X12 @ 
% 0.25/0.53              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.25/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.25/0.53  thf('12', plain,
% 0.25/0.53      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.25/0.53         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['8', '11'])).
% 0.25/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.25/0.53  thf('13', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.25/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.25/0.53  thf(t92_xboole_1, axiom,
% 0.25/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.25/0.53  thf('14', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.25/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.25/0.53  thf('15', plain,
% 0.25/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.25/0.53           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.25/0.53  thf('16', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.25/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.25/0.53  thf('17', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.25/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.25/0.53  thf('18', plain,
% 0.25/0.53      (((k3_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13', '16', '17'])).
% 0.25/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.25/0.53  thf('19', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.25/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.25/0.53  thf('20', plain,
% 0.25/0.53      (![X12 : $i, X13 : $i]:
% 0.25/0.53         ((k3_xboole_0 @ X12 @ X13)
% 0.25/0.53           = (k5_xboole_0 @ X12 @ 
% 0.25/0.53              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.25/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.25/0.53  thf('21', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((k3_xboole_0 @ X0 @ X0)
% 0.25/0.53           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.25/0.53  thf(idempotence_k3_xboole_0, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.25/0.53  thf('22', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.25/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.25/0.53  thf('23', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.25/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.25/0.53  thf('24', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.53      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.25/0.53  thf('25', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.25/0.53      inference('demod', [status(thm)], ['18', '24'])).
% 0.25/0.53  thf(t17_xboole_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.25/0.53  thf('26', plain,
% 0.25/0.53      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.25/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.25/0.53  thf('27', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.25/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.25/0.53  thf('28', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.25/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.25/0.53  thf('29', plain,
% 0.25/0.53      (![X42 : $i, X43 : $i]:
% 0.25/0.53         (((X43) = (k1_tarski @ X42))
% 0.25/0.53          | ((X43) = (k1_xboole_0))
% 0.25/0.53          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 0.25/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.25/0.53  thf('30', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.53          | ((X0) = (k1_xboole_0))
% 0.25/0.53          | ((X0) = (k1_tarski @ sk_A)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.25/0.53  thf('31', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.25/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.25/0.53  thf('32', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.25/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.25/0.53  thf('33', plain, ((((sk_C) = (sk_B)) | ((sk_C) = (k1_xboole_0)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['27', '32'])).
% 0.25/0.53  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('35', plain, (((sk_B) != (sk_C))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('36', plain, ($false),
% 0.25/0.53      inference('simplify_reflect-', [status(thm)], ['33', '34', '35'])).
% 0.25/0.53  
% 0.25/0.53  % SZS output end Refutation
% 0.25/0.53  
% 0.25/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
