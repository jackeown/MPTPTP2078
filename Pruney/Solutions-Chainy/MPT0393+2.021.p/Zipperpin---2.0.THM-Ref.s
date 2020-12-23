%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5iHW8Ow7e

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:43 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  501 ( 798 expanded)
%              Number of equality atoms :   56 (  86 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X36 @ X35 ) @ X35 )
      | ( r1_tarski @ X36 @ ( k1_setfam_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X30: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('5',plain,(
    ! [X31: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X31 ) @ ( k3_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X36 @ ( sk_C_2 @ X36 @ X35 ) )
      | ( r1_tarski @ X36 @ ( k1_setfam_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('18',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','22'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X21 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('27',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X21 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t5_setfam_1,axiom,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X34: $i] :
      ( ( ( k1_setfam_1 @ X34 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t5_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('31',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X18 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('42',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference('sup-',[status(thm)],['23','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5iHW8Ow7e
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 308 iterations in 0.149s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.38/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.60  thf(t6_setfam_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.38/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (![X35 : $i, X36 : $i]:
% 0.38/0.60         (((X35) = (k1_xboole_0))
% 0.38/0.60          | (r2_hidden @ (sk_C_2 @ X36 @ X35) @ X35)
% 0.38/0.60          | (r1_tarski @ X36 @ (k1_setfam_1 @ X35)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.38/0.60  thf(d1_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X16 @ X15)
% 0.38/0.60          | ((X16) = (X13))
% 0.38/0.60          | ((X15) != (k1_tarski @ X13)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X13 : $i, X16 : $i]:
% 0.38/0.60         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '2'])).
% 0.38/0.60  thf(t31_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.38/0.60  thf('4', plain, (![X30 : $i]: ((k3_tarski @ (k1_tarski @ X30)) = (X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.38/0.60  thf(t3_setfam_1, axiom,
% 0.38/0.60    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X31 : $i]: (r1_tarski @ (k1_setfam_1 @ X31) @ (k3_tarski @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.60  thf(d10_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X10 : $i, X12 : $i]:
% 0.38/0.60         (((X10) = (X12))
% 0.38/0.60          | ~ (r1_tarski @ X12 @ X10)
% 0.38/0.60          | ~ (r1_tarski @ X10 @ X12))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X35 : $i, X36 : $i]:
% 0.38/0.60         (((X35) = (k1_xboole_0))
% 0.38/0.60          | ~ (r1_tarski @ X36 @ (sk_C_2 @ X36 @ X35))
% 0.38/0.60          | (r1_tarski @ X36 @ (k1_setfam_1 @ X35)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ X0)
% 0.38/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('13', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.38/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('clc', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf(t11_setfam_1, conjecture,
% 0.38/0.60    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.38/0.60  thf('18', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf('20', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.60         (((X14) != (X13))
% 0.38/0.60          | (r2_hidden @ X14 @ X15)
% 0.38/0.60          | ((X15) != (k1_tarski @ X13)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.60  thf('22', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.38/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.60  thf('23', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['20', '22'])).
% 0.38/0.60  thf(d5_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.38/0.60         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.38/0.60          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.38/0.60          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['24'])).
% 0.38/0.60  thf(d2_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         (((X19) != (X21))
% 0.38/0.60          | (r2_hidden @ X19 @ X20)
% 0.38/0.60          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X18 : $i, X21 : $i]: (r2_hidden @ X21 @ (k2_tarski @ X21 @ X18))),
% 0.38/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.60  thf(t5_setfam_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.38/0.60       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X34 : $i]:
% 0.38/0.60         (((k1_setfam_1 @ X34) = (k1_xboole_0))
% 0.38/0.60          | ~ (r2_hidden @ k1_xboole_0 @ X34))),
% 0.38/0.60      inference('cnf', [status(esa)], [t5_setfam_1])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         (((X19) != (X18))
% 0.38/0.60          | (r2_hidden @ X19 @ X20)
% 0.38/0.60          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X18 : $i, X21 : $i]: (r2_hidden @ X18 @ (k2_tarski @ X21 @ X18))),
% 0.38/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.60  thf(t4_setfam_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X32 : $i, X33 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_setfam_1 @ X32) @ X33) | ~ (r2_hidden @ X33 @ X32))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.38/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.60  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['29', '33'])).
% 0.38/0.60  thf(d3_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.60          | (r2_hidden @ X0 @ X2)
% 0.38/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.38/0.60          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['25', '36'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.38/0.60          | ~ (r2_hidden @ X8 @ X6)
% 0.38/0.60          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.38/0.60          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))
% 0.38/0.60          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X2 @ k1_xboole_0) @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '39'])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.38/0.60          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['25', '36'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.38/0.60      inference('clc', [status(thm)], ['40', '41'])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.38/0.60          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.60      inference('condensation', [status(thm)], ['44'])).
% 0.38/0.60  thf('46', plain, ($false), inference('sup-', [status(thm)], ['23', '45'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
