%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qBvvWAxMcI

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 377 expanded)
%              Number of leaves         :   12 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  366 (4792 expanded)
%              Number of equality atoms :   84 (1136 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('11',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('23',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','12','24'])).

thf('26',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['9','25'])).

thf('27',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('29',plain,
    ( ( sk_B = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','26'])).

thf('31',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('32',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('35',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['29','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','36'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','26'])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ sk_C )
      = X2 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['29','35'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ sk_B )
      = X2 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('45',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('46',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qBvvWAxMcI
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:57:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 64 iterations in 0.020s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(t43_zfmisc_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.47          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.47          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.47          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.47             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.47             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.47             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.19/0.47  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.47  thf(t7_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '4'])).
% 0.19/0.47  thf(l3_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (((X9) = (k1_tarski @ X8))
% 0.19/0.47          | ((X9) = (k1_xboole_0))
% 0.19/0.47          | ~ (r1_tarski @ X9 @ (k1_tarski @ X8)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.47  thf('7', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('split', [status(esa)], ['8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.19/0.47      inference('split', [status(esa)], ['8'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['11'])).
% 0.19/0.47  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.47  thf('15', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (((X9) = (k1_tarski @ X8))
% 0.19/0.47          | ((X9) = (k1_xboole_0))
% 0.19/0.47          | ~ (r1_tarski @ X9 @ (k1_tarski @ X8)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('split', [status(esa)], ['18'])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.19/0.47         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['17', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['8'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      ((((sk_B) != (sk_B)))
% 0.19/0.47         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.47  thf('25', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['10', '12', '24'])).
% 0.19/0.47  thf('26', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['9', '25'])).
% 0.19/0.47  thf('27', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['7', '26'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      ((((sk_B) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.47  thf('30', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['7', '26'])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['18'])).
% 0.19/0.47  thf('32', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.47  thf('33', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C) = (k1_xboole_0)))),
% 0.19/0.47      inference('split', [status(esa)], ['18'])).
% 0.19/0.47  thf('35', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.19/0.47  thf('36', plain, (((sk_B) = (sk_C))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['29', '35'])).
% 0.19/0.47  thf('37', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '36'])).
% 0.19/0.47  thf(t1_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('38', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.47  thf('39', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['7', '26'])).
% 0.19/0.47  thf('40', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ sk_C) = (X2))),
% 0.19/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.47  thf('41', plain, (((sk_B) = (sk_C))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['29', '35'])).
% 0.19/0.47  thf('42', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ sk_B) = (X2))),
% 0.19/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.47  thf('43', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['37', '42'])).
% 0.19/0.47  thf('44', plain,
% 0.19/0.47      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.47      inference('split', [status(esa)], ['18'])).
% 0.19/0.47  thf('45', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.19/0.47  thf('46', plain, (((sk_B) != (k1_tarski @ sk_A))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['44', '45'])).
% 0.19/0.47  thf('47', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
