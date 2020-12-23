%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lphHJyUKmr

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 141 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  342 ( 973 expanded)
%              Number of equality atoms :   57 ( 208 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X25 ) )
      | ( X26 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X26 @ ( k1_tarski @ X25 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','10'])).

thf('12',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('23',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','23'])).

thf('25',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','10'])).

thf('26',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('33',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','10'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_C_1 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['12','41'])).

thf('43',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lphHJyUKmr
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 176 iterations in 0.078s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.55  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.55  thf(t44_zfmisc_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.55          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.55          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.56             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.38/0.56  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t7_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.56  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.38/0.56      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf(l3_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X25 : $i, X26 : $i]:
% 0.38/0.56         (((X26) = (k1_tarski @ X25))
% 0.38/0.56          | ((X26) = (k1_xboole_0))
% 0.38/0.56          | ~ (r1_tarski @ X26 @ (k1_tarski @ X25)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.56  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.38/0.56  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X25 : $i, X26 : $i]:
% 0.38/0.56         (((X26) = (k1_tarski @ X25))
% 0.38/0.56          | ((X26) = (o_0_0_xboole_0))
% 0.38/0.56          | ~ (r1_tarski @ X26 @ (k1_tarski @ X25)))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      ((((sk_B_1) = (o_0_0_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.38/0.56  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('10', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf('11', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['7', '10'])).
% 0.38/0.56  thf('12', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '11'])).
% 0.38/0.56  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t7_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.56  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf(d3_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.56          | (r2_hidden @ X0 @ X2)
% 0.38/0.56          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.38/0.56        | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['13', '19'])).
% 0.38/0.56  thf('21', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('22', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('23', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['20', '23'])).
% 0.38/0.56  thf('25', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['7', '10'])).
% 0.38/0.56  thf('26', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.56  thf('27', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['7', '10'])).
% 0.38/0.56  thf(d1_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X14 @ X13)
% 0.38/0.56          | ((X14) = (X11))
% 0.38/0.56          | ((X13) != (k1_tarski @ X11)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X11 : $i, X14 : $i]:
% 0.38/0.56         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['27', '29'])).
% 0.38/0.56  thf('31', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['26', '30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X6 : $i]: (((X6) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf(l1_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X22 : $i, X24 : $i]:
% 0.38/0.56         ((r1_tarski @ (k1_tarski @ X22) @ X24) | ~ (r2_hidden @ X22 @ X24))),
% 0.38/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 0.38/0.56        | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['31', '34'])).
% 0.38/0.56  thf('36', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['7', '10'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (((r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_C_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain, (((sk_C_1) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('39', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf(t12_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]:
% 0.38/0.56         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.56  thf('41', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.56  thf('42', plain, (((sk_B_1) = (sk_C_1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['12', '41'])).
% 0.38/0.56  thf('43', plain, (((sk_B_1) != (sk_C_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('44', plain, ($false),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
