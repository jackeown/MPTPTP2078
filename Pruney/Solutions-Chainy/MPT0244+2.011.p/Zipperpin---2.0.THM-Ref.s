%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pMF2hOyUPW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:11 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  457 ( 789 expanded)
%              Number of equality atoms :   56 ( 112 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('26',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('29',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('30',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('36',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_A != k1_xboole_0 )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('48',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','19','40','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pMF2hOyUPW
% 0.13/0.37  % Computer   : n021.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:39:20 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 195 iterations in 0.082s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.56  thf(t39_zfmisc_1, conjecture,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i,B:$i]:
% 0.24/0.56        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.56          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.24/0.56  thf('0', plain,
% 0.24/0.56      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.24/0.56       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.56      inference('split', [status(esa)], ['0'])).
% 0.24/0.56  thf(t3_boole, axiom,
% 0.24/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.56  thf('2', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.56  thf(t83_xboole_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.56  thf('3', plain,
% 0.24/0.56      (![X13 : $i, X15 : $i]:
% 0.24/0.56         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.56  thf('5', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.24/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.24/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.24/0.56  thf('6', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.56  thf('7', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.24/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.56  thf('8', plain,
% 0.24/0.56      (![X13 : $i, X14 : $i]:
% 0.24/0.56         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.24/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.56  thf('9', plain,
% 0.24/0.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.56  thf(l32_xboole_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.56  thf('10', plain,
% 0.24/0.56      (![X9 : $i, X10 : $i]:
% 0.24/0.56         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.24/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.56  thf('11', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.56  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      ((((sk_A) = (k1_tarski @ sk_B))
% 0.24/0.56        | ((sk_A) = (k1_xboole_0))
% 0.24/0.56        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('split', [status(esa)], ['13'])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.56         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('split', [status(esa)], ['0'])).
% 0.24/0.56  thf('16', plain,
% 0.24/0.56      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.24/0.56         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.24/0.56             (((sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['12', '16'])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      ((((sk_A) != (k1_tarski @ sk_B))
% 0.24/0.56        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('19', plain,
% 0.24/0.56      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.56       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.56      inference('split', [status(esa)], ['18'])).
% 0.24/0.56  thf(l27_zfmisc_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (![X25 : $i, X26 : $i]:
% 0.24/0.56         ((r1_xboole_0 @ (k1_tarski @ X25) @ X26) | (r2_hidden @ X25 @ X26))),
% 0.24/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.56  thf('22', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X13 : $i, X14 : $i]:
% 0.24/0.56         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.24/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.56  thf('24', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r2_hidden @ X0 @ X1)
% 0.24/0.56          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.24/0.56  thf('25', plain,
% 0.24/0.56      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('split', [status(esa)], ['13'])).
% 0.24/0.56  thf('26', plain,
% 0.24/0.56      (![X9 : $i, X11 : $i]:
% 0.24/0.56         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.24/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.56  thf('28', plain,
% 0.24/0.56      (((((sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_A)))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup+', [status(thm)], ['24', '27'])).
% 0.24/0.56  thf(l1_zfmisc_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      (![X22 : $i, X24 : $i]:
% 0.24/0.56         ((r1_tarski @ (k1_tarski @ X22) @ X24) | ~ (r2_hidden @ X22 @ X24))),
% 0.24/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.24/0.56  thf('30', plain,
% 0.24/0.56      (((((sk_A) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.56  thf('31', plain,
% 0.24/0.56      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('split', [status(esa)], ['13'])).
% 0.24/0.56  thf(d10_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.56  thf('32', plain,
% 0.24/0.56      (![X6 : $i, X8 : $i]:
% 0.24/0.56         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('33', plain,
% 0.24/0.56      (((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.24/0.56         | ((k1_tarski @ sk_B) = (sk_A))))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.56  thf('34', plain,
% 0.24/0.56      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (sk_A))))
% 0.24/0.56         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['30', '33'])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('split', [status(esa)], ['18'])).
% 0.24/0.56  thf('36', plain,
% 0.24/0.56      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0))))
% 0.24/0.56         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.24/0.56             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.56  thf('37', plain,
% 0.24/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.24/0.56         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.24/0.56             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('simplify', [status(thm)], ['36'])).
% 0.24/0.56  thf('38', plain,
% 0.24/0.56      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('split', [status(esa)], ['0'])).
% 0.24/0.56  thf('39', plain,
% 0.24/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.24/0.56         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.24/0.56             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.24/0.56             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.56       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.24/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.24/0.56  thf('41', plain,
% 0.24/0.56      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('42', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.24/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.24/0.56  thf('43', plain,
% 0.24/0.56      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('split', [status(esa)], ['13'])).
% 0.24/0.56  thf('44', plain,
% 0.24/0.56      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.56         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('split', [status(esa)], ['0'])).
% 0.24/0.56  thf('45', plain,
% 0.24/0.56      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.24/0.56         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.24/0.56             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.24/0.56  thf('46', plain,
% 0.24/0.56      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.56       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['42', '45'])).
% 0.24/0.56  thf('47', plain,
% 0.24/0.56      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.56       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.24/0.56      inference('split', [status(esa)], ['13'])).
% 0.24/0.56  thf('48', plain, ($false),
% 0.24/0.56      inference('sat_resolution*', [status(thm)],
% 0.24/0.56                ['1', '17', '19', '40', '46', '47'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
