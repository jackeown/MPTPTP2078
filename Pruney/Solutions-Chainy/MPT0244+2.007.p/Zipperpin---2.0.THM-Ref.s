%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QElTBzzLgF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 290 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  377 (2300 expanded)
%              Number of equality atoms :   49 ( 352 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('7',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','17','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('27',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','21'])).

thf('38',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['27','29'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('41',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['20','43'])).

thf('45',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['42','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QElTBzzLgF
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 79 iterations in 0.036s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(t7_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.50  thf(t39_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.50          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.50       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('8', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('9', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) & 
% 0.20/0.50             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) | 
% 0.20/0.50       ~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf('13', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['7', '12'])).
% 0.20/0.50  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.20/0.50        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['5', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((sk_A) = (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('19', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.20/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.50  thf('20', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '17', '19'])).
% 0.20/0.50  thf('21', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['20'])).
% 0.20/0.50  thf('22', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '24'])).
% 0.20/0.50  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.20/0.50  thf('27', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.50          | ((X12) = (X9))
% 0.20/0.50          | ((X11) != (k1_tarski @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X9 : $i, X12 : $i]:
% 0.20/0.50         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.50  thf(l1_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X20 : $i, X22 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tarski @ X20) @ X22) | ~ (r2_hidden @ X20 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X5 : $i, X7 : $i]:
% 0.20/0.50         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.20/0.50          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))
% 0.20/0.50        | ((sk_A) = (k1_tarski @ (sk_B @ sk_A)))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.50  thf('37', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.20/0.50  thf('38', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((sk_A) = (k1_tarski @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.50  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.20/0.50        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((((sk_A) != (k1_tarski @ sk_B_1)))
% 0.20/0.50         <= (~ (((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 0.20/0.50       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['41'])).
% 0.20/0.50  thf('44', plain, (~ (((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['20', '43'])).
% 0.20/0.50  thf('45', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['42', '44'])).
% 0.20/0.50  thf('46', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['39', '40', '45'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
