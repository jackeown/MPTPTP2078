%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sTM6FqMgiU

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 366 expanded)
%              Number of leaves         :   15 (  99 expanded)
%              Depth                    :   21
%              Number of atoms          :  534 (5339 expanded)
%              Number of equality atoms :  113 (1212 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14
        = ( k2_tarski @ X12 @ X13 ) )
      | ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14
        = ( k1_tarski @ X12 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_tarski @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('24',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('35',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','25','36'])).

thf('38',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['22','37'])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('41',plain,
    ( ( sk_B = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','38'])).

thf('43',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['41','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2','48','51'])).

thf('53',plain,
    ( $false
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('55',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sTM6FqMgiU
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 256 iterations in 0.137s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(t43_zfmisc_1, conjecture,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.59          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.59          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.59          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.59        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.59             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.59             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.59             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(d10_xboole_0, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.59  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.59      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.59  thf(t10_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.59  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t69_enumset1, axiom,
% 0.21/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.59  thf('8', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf(l45_zfmisc_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.59       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.59            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         (((X14) = (k2_tarski @ X12 @ X13))
% 0.21/0.59          | ((X14) = (k1_tarski @ X13))
% 0.21/0.59          | ((X14) = (k1_tarski @ X12))
% 0.21/0.59          | ((X14) = (k1_xboole_0))
% 0.21/0.59          | ~ (r1_tarski @ X14 @ (k2_tarski @ X12 @ X13)))),
% 0.21/0.59      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.59          | ((X1) = (k1_xboole_0))
% 0.21/0.59          | ((X1) = (k1_tarski @ X0))
% 0.21/0.59          | ((X1) = (k1_tarski @ X0))
% 0.21/0.59          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.59          | ((X1) = (k1_tarski @ X0))
% 0.21/0.59          | ((X1) = (k1_xboole_0))
% 0.21/0.59          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.59          | ((X0) = (k1_xboole_0))
% 0.21/0.59          | ((X0) = (k1_tarski @ sk_A))
% 0.21/0.59          | ((X0) = (k2_tarski @ sk_A @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.59  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('14', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.59          | ((X0) = (k1_xboole_0))
% 0.21/0.59          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.59          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((X0) = (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.59          | ((X0) = (k1_xboole_0))
% 0.21/0.59          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['6', '17'])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('split', [status(esa)], ['19'])).
% 0.21/0.59  thf('21', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.21/0.59         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.59      inference('split', [status(esa)], ['19'])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('split', [status(esa)], ['24'])).
% 0.21/0.59  thf(t7_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.21/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((X0) = (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.59          | ((X0) = (k1_xboole_0))
% 0.21/0.59          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.59  thf('28', plain,
% 0.21/0.59      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.59  thf('29', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('30', plain,
% 0.21/0.59      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.21/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.59  thf('33', plain,
% 0.21/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.59      inference('split', [status(esa)], ['19'])).
% 0.21/0.59  thf('35', plain,
% 0.21/0.59      ((((sk_B) != (sk_B)))
% 0.21/0.59         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.59  thf('37', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['23', '25', '36'])).
% 0.21/0.59  thf('38', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.59      inference('simpl_trail', [status(thm)], ['22', '37'])).
% 0.21/0.59  thf('39', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['18', '38'])).
% 0.21/0.59  thf('40', plain,
% 0.21/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.59  thf('41', plain,
% 0.21/0.59      ((((sk_B) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.59  thf('42', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['18', '38'])).
% 0.21/0.59  thf('43', plain,
% 0.21/0.59      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('44', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.59  thf('45', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('47', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.21/0.59  thf('48', plain, (((sk_B) = (sk_C))),
% 0.21/0.59      inference('simpl_trail', [status(thm)], ['41', '47'])).
% 0.21/0.59  thf('49', plain,
% 0.21/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.59  thf(t1_boole, axiom,
% 0.21/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.59  thf('50', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      ((![X0 : $i]: ((k2_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.21/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.59  thf('52', plain,
% 0.21/0.59      ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('demod', [status(thm)], ['1', '2', '48', '51'])).
% 0.21/0.59  thf('53', plain, (($false) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.59  thf('54', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.21/0.59  thf('55', plain, ($false),
% 0.21/0.59      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
