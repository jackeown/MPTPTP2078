%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pnWEj0Ut6j

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:21 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 266 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  574 (3310 expanded)
%              Number of equality atoms :  106 ( 745 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','16'])).

thf('18',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('27',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    k1_xboole_0
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['18','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('36',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('38',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','38','41'])).

thf('43',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('44',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('48',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['42','48'])).

thf('50',plain,(
    k1_xboole_0
 != ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('55',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['51','59'])).

thf('61',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['50','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pnWEj0Ut6j
% 0.15/0.38  % Computer   : n010.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:07:14 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 786 iterations in 0.709s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.00/1.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.00/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.00/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.20  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.00/1.20  thf(t43_zfmisc_1, conjecture,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.00/1.20          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.00/1.20          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.00/1.20          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.00/1.20        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.00/1.20             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.00/1.20             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.00/1.20             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.00/1.20         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('split', [status(esa)], ['0'])).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.00/1.20      inference('split', [status(esa)], ['0'])).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('split', [status(esa)], ['3'])).
% 1.00/1.20  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(t7_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.00/1.20  thf('7', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 1.00/1.20      inference('sup+', [status(thm)], ['5', '6'])).
% 1.00/1.20  thf(l3_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.00/1.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (![X21 : $i, X22 : $i]:
% 1.00/1.20         (((X22) = (k1_tarski @ X21))
% 1.00/1.20          | ((X22) = (k1_xboole_0))
% 1.00/1.20          | ~ (r1_tarski @ X22 @ (k1_tarski @ X21)))),
% 1.00/1.20      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.00/1.20  thf('9', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.00/1.20  thf('10', plain,
% 1.00/1.20      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('11', plain,
% 1.00/1.20      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('split', [status(esa)], ['10'])).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 1.00/1.20         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['9', '11'])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.00/1.20      inference('split', [status(esa)], ['0'])).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.00/1.20         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.00/1.20  thf('16', plain,
% 1.00/1.20      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['15'])).
% 1.00/1.20  thf('17', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('sat_resolution*', [status(thm)], ['2', '4', '16'])).
% 1.00/1.20  thf('18', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.00/1.20      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 1.00/1.20  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(commutativity_k2_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.00/1.20  thf('20', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.00/1.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.00/1.20  thf('22', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['20', '21'])).
% 1.00/1.20  thf('23', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 1.00/1.20      inference('sup+', [status(thm)], ['19', '22'])).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      (![X21 : $i, X22 : $i]:
% 1.00/1.20         (((X22) = (k1_tarski @ X21))
% 1.00/1.20          | ((X22) = (k1_xboole_0))
% 1.00/1.20          | ~ (r1_tarski @ X22 @ (k1_tarski @ X21)))),
% 1.00/1.20      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      ((((sk_C_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.00/1.20  thf('26', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.00/1.20      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 1.00/1.20  thf('27', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.00/1.20      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.00/1.20  thf('28', plain, (((k1_xboole_0) != (k1_tarski @ sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['18', '27'])).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.00/1.20  thf('30', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.00/1.20         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('sup+', [status(thm)], ['29', '30'])).
% 1.00/1.20  thf('32', plain,
% 1.00/1.20      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.00/1.20         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('sup+', [status(thm)], ['29', '30'])).
% 1.00/1.20  thf('33', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['20', '21'])).
% 1.00/1.20  thf('34', plain,
% 1.00/1.20      (((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A)))
% 1.00/1.20         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('sup+', [status(thm)], ['32', '33'])).
% 1.00/1.20  thf('35', plain,
% 1.00/1.20      (![X21 : $i, X22 : $i]:
% 1.00/1.20         (((X22) = (k1_tarski @ X21))
% 1.00/1.20          | ((X22) = (k1_xboole_0))
% 1.00/1.20          | ~ (r1_tarski @ X22 @ (k1_tarski @ X21)))),
% 1.00/1.20      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.00/1.20  thf('36', plain,
% 1.00/1.20      (((((sk_C_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_tarski @ sk_A))))
% 1.00/1.20         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['34', '35'])).
% 1.00/1.20  thf('37', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.00/1.20      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 1.00/1.20  thf('38', plain,
% 1.00/1.20      ((((sk_C_1) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 1.00/1.20  thf(t69_enumset1, axiom,
% 1.00/1.20    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.00/1.20  thf('39', plain,
% 1.00/1.20      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 1.00/1.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.00/1.20  thf(l51_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.00/1.20  thf('40', plain,
% 1.00/1.20      (![X24 : $i, X25 : $i]:
% 1.00/1.20         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.00/1.20      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.00/1.20  thf('41', plain,
% 1.00/1.20      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['39', '40'])).
% 1.00/1.20  thf('42', plain,
% 1.00/1.20      ((((k1_tarski @ sk_A) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 1.00/1.20         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.00/1.20      inference('demod', [status(thm)], ['31', '38', '41'])).
% 1.00/1.20  thf('43', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.00/1.20      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.00/1.20  thf('44', plain,
% 1.00/1.20      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.00/1.20      inference('split', [status(esa)], ['10'])).
% 1.00/1.20  thf('45', plain,
% 1.00/1.20      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['43', '44'])).
% 1.00/1.20  thf('46', plain, ((((sk_C_1) = (k1_xboole_0)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['45'])).
% 1.00/1.20  thf('47', plain,
% 1.00/1.20      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C_1) = (k1_xboole_0)))),
% 1.00/1.20      inference('split', [status(esa)], ['10'])).
% 1.00/1.20  thf('48', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 1.00/1.20  thf('49', plain,
% 1.00/1.20      (((k1_tarski @ sk_A) = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 1.00/1.20      inference('simpl_trail', [status(thm)], ['42', '48'])).
% 1.00/1.20  thf('50', plain,
% 1.00/1.20      (((k1_xboole_0) != (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 1.00/1.20      inference('demod', [status(thm)], ['28', '49'])).
% 1.00/1.20  thf('51', plain,
% 1.00/1.20      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['39', '40'])).
% 1.00/1.20  thf(d3_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.20           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.00/1.20  thf('52', plain,
% 1.00/1.20      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.00/1.20         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 1.00/1.20          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 1.00/1.20          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.00/1.20      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.00/1.20  thf('53', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.00/1.20          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 1.00/1.20          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 1.00/1.20      inference('eq_fact', [status(thm)], ['52'])).
% 1.00/1.20  thf('54', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.00/1.20      inference('eq_fact', [status(thm)], ['53'])).
% 1.00/1.20  thf('55', plain,
% 1.00/1.20      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.00/1.20         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.00/1.20          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 1.00/1.20          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.00/1.20      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.00/1.20  thf('56', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.00/1.20          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.00/1.20          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['54', '55'])).
% 1.00/1.20  thf('57', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.00/1.20          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['56'])).
% 1.00/1.20  thf('58', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.00/1.20      inference('eq_fact', [status(thm)], ['53'])).
% 1.00/1.20  thf('59', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.00/1.20      inference('clc', [status(thm)], ['57', '58'])).
% 1.00/1.20  thf('60', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.00/1.20      inference('demod', [status(thm)], ['51', '59'])).
% 1.00/1.20  thf('61', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.00/1.20      inference('demod', [status(thm)], ['50', '60'])).
% 1.00/1.20  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
