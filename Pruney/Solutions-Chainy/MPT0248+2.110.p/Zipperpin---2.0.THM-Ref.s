%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8wDGGGtcN4

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:34 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 285 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  431 (4019 expanded)
%              Number of equality atoms :   94 ( 940 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('18',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','19','30'])).

thf('32',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['16','31'])).

thf('33',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['12','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('35',plain,
    ( ( sk_B = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['12','32'])).

thf('37',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['35','41'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2','42','45'])).

thf('47',plain,
    ( $false
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('49',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8wDGGGtcN4
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:38:14 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 60 iterations in 0.030s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(t43_zfmisc_1, conjecture,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.24/0.52          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.52          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.52          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.52        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.24/0.52             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.52             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.52             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(d10_xboole_0, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.52  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.24/0.52  thf(t10_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.52         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.52  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(l3_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (((X13) = (k1_tarski @ X12))
% 0.24/0.52          | ((X13) = (k1_xboole_0))
% 0.24/0.52          | ~ (r1_tarski @ X13 @ (k1_tarski @ X12)))),
% 0.24/0.52      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.24/0.52          | ((X0) = (k1_xboole_0))
% 0.24/0.52          | ((X0) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.24/0.52          | ((X0) = (k1_xboole_0))
% 0.24/0.52          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.24/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      ((((sk_C) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['6', '11'])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('split', [status(esa)], ['13'])).
% 0.24/0.52  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.24/0.52         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('split', [status(esa)], ['13'])).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('split', [status(esa)], ['18'])).
% 0.24/0.52  thf(t7_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.24/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.24/0.52          | ((X0) = (k1_xboole_0))
% 0.24/0.52          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.24/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf('23', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.24/0.52         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.24/0.52         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['13'])).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      ((((sk_B) != (sk_B)))
% 0.24/0.52         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.24/0.52  thf('31', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('sat_resolution*', [status(thm)], ['17', '19', '30'])).
% 0.24/0.52  thf('32', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('simpl_trail', [status(thm)], ['16', '31'])).
% 0.24/0.52  thf('33', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['12', '32'])).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      ((((sk_B) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.24/0.52  thf('36', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['12', '32'])).
% 0.24/0.52  thf('37', plain,
% 0.24/0.52      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('38', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.24/0.52  thf('39', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.24/0.52  thf('40', plain,
% 0.24/0.52      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C) = (k1_xboole_0)))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('41', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.24/0.52  thf('42', plain, (((sk_B) = (sk_C))),
% 0.24/0.52      inference('simpl_trail', [status(thm)], ['35', '41'])).
% 0.24/0.52  thf('43', plain,
% 0.24/0.52      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.52  thf(t1_boole, axiom,
% 0.24/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.52  thf('44', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.24/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.52  thf('45', plain,
% 0.24/0.52      ((![X0 : $i]: ((k2_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.24/0.52         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('sup+', [status(thm)], ['43', '44'])).
% 0.24/0.52  thf('46', plain,
% 0.24/0.52      ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['1', '2', '42', '45'])).
% 0.24/0.52  thf('47', plain, (($false) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['46'])).
% 0.24/0.52  thf('48', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.24/0.52  thf('49', plain, ($false),
% 0.24/0.52      inference('simpl_trail', [status(thm)], ['47', '48'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
