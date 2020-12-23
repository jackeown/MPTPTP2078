%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.foZlLW7G3c

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 122 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 ( 933 expanded)
%              Number of equality atoms :   45 ( 127 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('21',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','14'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('33',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_B )
      = sk_A )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('36',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','16','38','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.foZlLW7G3c
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 120 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(t39_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.49          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.49  thf('2', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.49  thf('4', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t83_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ sk_B))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.20/0.49             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((sk_A) != (k1_tarski @ sk_B))
% 0.20/0.49        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X2 : $i, X4 : $i]:
% 0.20/0.49         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.49         | ((k1_tarski @ sk_B) = (sk_A))))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X5 : $i, X7 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf(l27_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k1_tarski @ X21) @ X22) | (r2_hidden @ X21 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ X1)
% 0.20/0.49          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['22', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('30', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '14'])).
% 0.20/0.49  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_A))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 0.20/0.49  thf(l1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X18 : $i, X20 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X18) @ X20) | ~ (r2_hidden @ X18 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((((k1_tarski @ sk_B) = (sk_A)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['15'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)))
% 0.20/0.49         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.20/0.49             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('40', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.20/0.49             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.49       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.49       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('46', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)],
% 0.20/0.49                ['1', '14', '16', '38', '44', '45'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
