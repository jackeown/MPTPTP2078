%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6te0asrZE5

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 217 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  373 (2619 expanded)
%              Number of equality atoms :   80 ( 608 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('13',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['12','14','26'])).

thf('28',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['11','27'])).

thf('29',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['9','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('31',plain,
    ( ( sk_B = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['9','28'])).

thf('33',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('34',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('37',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['0','38','41'])).

thf('43',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('44',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('45',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6te0asrZE5
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 78 iterations in 0.035s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(t43_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.51          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.51          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.51          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.51             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.51             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.51             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.22/0.51  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t1_boole, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.51  thf('2', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.51  thf(t7_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.51  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf(t10_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.22/0.51      inference('sup+', [status(thm)], ['1', '6'])).
% 0.22/0.51  thf(l3_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i]:
% 0.22/0.51         (((X15) = (k1_tarski @ X14))
% 0.22/0.51          | ((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.51  thf('9', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.22/0.51      inference('split', [status(esa)], ['10'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['13'])).
% 0.22/0.51  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.51  thf('17', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i]:
% 0.22/0.51         (((X15) = (k1_tarski @ X14))
% 0.22/0.51          | ((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.22/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.22/0.51      inference('split', [status(esa)], ['10'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((((sk_B) != (sk_B)))
% 0.22/0.51         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.51  thf('27', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['12', '14', '26'])).
% 0.22/0.51  thf('28', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['11', '27'])).
% 0.22/0.51  thf('29', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['9', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((((sk_B) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['9', '28'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.22/0.51      inference('split', [status(esa)], ['20'])).
% 0.22/0.51  thf('34', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C) = (k1_xboole_0)))),
% 0.22/0.51      inference('split', [status(esa)], ['20'])).
% 0.22/0.51  thf('37', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain, (((sk_B) = (sk_C))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['31', '37'])).
% 0.22/0.51  thf('39', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf(t12_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.51  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '38', '41'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['20'])).
% 0.22/0.51  thf('44', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('45', plain, (((sk_B) != (k1_tarski @ sk_A))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['43', '44'])).
% 0.22/0.51  thf('46', plain, ($false),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
