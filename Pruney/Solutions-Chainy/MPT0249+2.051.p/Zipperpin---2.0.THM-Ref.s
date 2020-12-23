%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1DMMULKek5

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:45 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 168 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  383 (1394 expanded)
%              Number of equality atoms :   59 ( 278 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('19',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
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

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X50 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r2_hidden @ X50 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C ) @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['19','26'])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_1 = sk_C ),
    inference('sup+',[status(thm)],['8','42'])).

thf('44',plain,(
    sk_B_1 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1DMMULKek5
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 537 iterations in 0.201s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(t44_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.64          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.64             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.46/0.64  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t7_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(l3_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.46/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X45 : $i, X46 : $i]:
% 0.46/0.64         (((X46) = (k1_tarski @ X45))
% 0.46/0.64          | ((X46) = (k1_xboole_0))
% 0.46/0.64          | ~ (r1_tarski @ X46 @ (k1_tarski @ X45)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('6', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('7', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '7'])).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf(d3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X2)
% 0.46/0.64          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.46/0.64         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X0) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.46/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['10', '14'])).
% 0.46/0.64  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('17', plain, ((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('18', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('19', plain, ((r2_hidden @ (sk_B @ sk_C) @ sk_B_1)),
% 0.46/0.64      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf(d2_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X15 @ X13)
% 0.46/0.64          | ((X15) = (X14))
% 0.46/0.64          | ((X15) = (X11))
% 0.46/0.64          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.46/0.64         (((X15) = (X11))
% 0.46/0.64          | ((X15) = (X14))
% 0.46/0.64          | ~ (r2_hidden @ X15 @ (k2_tarski @ X14 @ X11)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '25'])).
% 0.46/0.64  thf('27', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('29', plain, (((r2_hidden @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('31', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf(t38_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.46/0.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X50 : $i, X52 : $i, X53 : $i]:
% 0.46/0.64         ((r1_tarski @ (k2_tarski @ X50 @ X52) @ X53)
% 0.46/0.64          | ~ (r2_hidden @ X52 @ X53)
% 0.46/0.64          | ~ (r2_hidden @ X50 @ X53))),
% 0.46/0.64      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ sk_C)
% 0.46/0.64          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      ((((sk_C) = (k1_xboole_0))
% 0.46/0.64        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C) @ sk_A) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '33'])).
% 0.46/0.64  thf('35', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '26'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('37', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('38', plain, ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.46/0.64  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('40', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf(t12_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.64  thf('42', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C) = (sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain, (((sk_B_1) = (sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['8', '42'])).
% 0.46/0.64  thf('44', plain, (((sk_B_1) != (sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('45', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
