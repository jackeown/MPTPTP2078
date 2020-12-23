%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mpN4bBW3nu

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:43 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 109 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  498 ( 836 expanded)
%              Number of equality atoms :   49 (  83 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X21 @ X20 ) @ X20 )
      | ( r1_tarski @ X21 @ ( k1_setfam_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k1_setfam_1 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ ( sk_C_2 @ X21 @ X20 ) )
      | ( r1_tarski @ X21 @ ( k1_setfam_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('21',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ ( k1_tarski @ X15 ) )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('34',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
       != sk_A )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    $false ),
    inference('sup-',[status(thm)],['25','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mpN4bBW3nu
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 266 iterations in 0.156s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.44/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(t6_setfam_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.44/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.44/0.61  thf('0', plain,
% 0.44/0.61      (![X20 : $i, X21 : $i]:
% 0.44/0.61         (((X20) = (k1_xboole_0))
% 0.44/0.61          | (r2_hidden @ (sk_C_2 @ X21 @ X20) @ X20)
% 0.44/0.61          | (r1_tarski @ X21 @ (k1_setfam_1 @ X20)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.44/0.61  thf(d1_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X10 @ X9)
% 0.44/0.61          | ((X10) = (X7))
% 0.44/0.61          | ((X9) != (k1_tarski @ X7)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X7 : $i, X10 : $i]:
% 0.44/0.61         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.44/0.61          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '2'])).
% 0.44/0.61  thf(d10_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.61         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.61  thf('7', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.44/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.44/0.61  thf(t8_setfam_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.44/0.61       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X22 @ X23)
% 0.44/0.61          | ~ (r1_tarski @ X22 @ X24)
% 0.44/0.61          | (r1_tarski @ (k1_setfam_1 @ X23) @ X24))),
% 0.44/0.61      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.44/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['5', '9'])).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      (![X4 : $i, X6 : $i]:
% 0.44/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.44/0.61          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['3', '12'])).
% 0.44/0.61  thf('14', plain,
% 0.44/0.61      (![X20 : $i, X21 : $i]:
% 0.44/0.61         (((X20) = (k1_xboole_0))
% 0.44/0.61          | ~ (r1_tarski @ X21 @ (sk_C_2 @ X21 @ X20))
% 0.44/0.61          | (r1_tarski @ X21 @ (k1_setfam_1 @ X20)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_tarski @ X0 @ X0)
% 0.44/0.61          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.44/0.61          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.44/0.61          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.44/0.61          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.44/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.44/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('clc', [status(thm)], ['18', '19'])).
% 0.44/0.61  thf(t11_setfam_1, conjecture,
% 0.44/0.61    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.44/0.61  thf('21', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.44/0.61  thf('24', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.44/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.44/0.61  thf('25', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.44/0.61      inference('sup+', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf(d3_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.61  thf('26', plain,
% 0.44/0.61      (![X1 : $i, X3 : $i]:
% 0.44/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf(t64_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.44/0.61       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.61         ((r2_hidden @ X16 @ X17)
% 0.44/0.61          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 0.44/0.61      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 0.44/0.61             X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      (![X1 : $i, X3 : $i]:
% 0.44/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 0.44/0.61          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      (![X1 : $i, X3 : $i]:
% 0.44/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf(l3_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.44/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      (![X14 : $i, X15 : $i]:
% 0.44/0.61         ((r1_tarski @ X14 @ (k1_tarski @ X15)) | ((X14) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.44/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.61          | (r2_hidden @ X0 @ X2)
% 0.44/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.44/0.61          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['32', '36'])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      (![X7 : $i, X10 : $i]:
% 0.44/0.61         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.44/0.61  thf('39', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.44/0.61  thf('40', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((sk_C @ X0 @ k1_xboole_0) != (sk_A))
% 0.44/0.61          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.44/0.61  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('clc', [status(thm)], ['41', '42'])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      (![X4 : $i, X6 : $i]:
% 0.44/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['31', '45'])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.61         (((X16) != (X18))
% 0.44/0.61          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 0.44/0.61      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.44/0.61  thf('48', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i]:
% 0.44/0.61         ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.61  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['46', '48'])).
% 0.44/0.61  thf('50', plain, ($false), inference('sup-', [status(thm)], ['25', '49'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
