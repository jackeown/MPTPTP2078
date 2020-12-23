%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u6dqsWT7Vf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 200 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  556 (2653 expanded)
%              Number of equality atoms :  102 ( 594 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X14 @ ( k2_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
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

thf('6',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X48
        = ( k2_tarski @ X46 @ X47 ) )
      | ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48
        = ( k1_tarski @ X46 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k2_tarski @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('19',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X30: $i] :
      ( ( k5_xboole_0 @ X30 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('40',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('44',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','41','45'])).

thf('47',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['38','46'])).

thf('48',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('51',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','51'])).

thf('53',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['38','46'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u6dqsWT7Vf
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 348 iterations in 0.122s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('1', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.38/0.57      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.57  thf(t10_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X14 @ X15)
% 0.38/0.57          | (r1_tarski @ X14 @ (k2_xboole_0 @ X16 @ X15)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(t43_zfmisc_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.57          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.38/0.57          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.38/0.57          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.57             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.38/0.57             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.38/0.57             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.38/0.57  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t69_enumset1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.57  thf('5', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf(l45_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.38/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.38/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.38/0.57         (((X48) = (k2_tarski @ X46 @ X47))
% 0.38/0.57          | ((X48) = (k1_tarski @ X47))
% 0.38/0.57          | ((X48) = (k1_tarski @ X46))
% 0.38/0.57          | ((X48) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X48 @ (k2_tarski @ X46 @ X47)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_xboole_0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_xboole_0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.38/0.57          | ((X0) = (k1_xboole_0))
% 0.38/0.57          | ((X0) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '10'])).
% 0.38/0.57  thf('12', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.38/0.57          | ((X0) = (k1_xboole_0))
% 0.38/0.57          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      ((((sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.38/0.57        | ((sk_C_2) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['15'])).
% 0.38/0.57  thf(t7_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.38/0.57          | ((X0) = (k1_xboole_0))
% 0.38/0.57          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.38/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.38/0.57         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['15'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.38/0.57         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.38/0.57         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.57  thf(d3_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf(t92_xboole_1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('26', plain, (![X30 : $i]: ((k5_xboole_0 @ X30 @ X30) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.57  thf(t1_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.38/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X4 @ X5)
% 0.38/0.57          | ~ (r2_hidden @ X4 @ X6)
% 0.38/0.57          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.38/0.57          | ~ (r2_hidden @ X1 @ X0)
% 0.38/0.57          | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.57  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.57      inference('condensation', [status(thm)], ['29'])).
% 0.38/0.57  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '30'])).
% 0.38/0.57  thf(t12_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.57  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.38/0.57         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['24', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.38/0.57         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['35'])).
% 0.38/0.57  thf('37', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      ((((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.38/0.57         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.57      inference('split', [status(esa)], ['35'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.38/0.57       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['35'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      ((((sk_B_1) != (sk_B_1)))
% 0.38/0.57         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.38/0.57             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.57  thf('46', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['39', '41', '45'])).
% 0.38/0.57  thf('47', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['38', '46'])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['34', '47'])).
% 0.38/0.57  thf('49', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['15'])).
% 0.38/0.57  thf('51', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('52', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['16', '51'])).
% 0.38/0.57  thf('53', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['38', '46'])).
% 0.38/0.57  thf('54', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['14', '52', '53'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
