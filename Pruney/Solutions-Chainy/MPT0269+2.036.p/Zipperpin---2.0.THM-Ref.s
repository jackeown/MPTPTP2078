%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2wYna9qWyF

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:07 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 723 expanded)
%              Number of leaves         :   12 ( 196 expanded)
%              Depth                    :   25
%              Number of atoms          :  673 (7262 expanded)
%              Number of equality atoms :   93 ( 961 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ X14 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ k1_xboole_0 )
      | ( ( sk_C @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = sk_B )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = sk_B )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( sk_C @ sk_A @ sk_B )
      = sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C @ sk_A @ sk_B )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
       != X6 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( sk_C @ sk_A @ sk_B )
     != sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C @ sk_A @ sk_B )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B != sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
       != X6 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
       != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
       != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) )
      | ( ( sk_C @ sk_A @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) )
       != ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) )
      | ( ( sk_C @ sk_A @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) )
       != ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['52','60'])).

thf('62',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2wYna9qWyF
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 311 iterations in 0.305s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.79  thf(d5_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.58/0.79       ( ![D:$i]:
% 0.58/0.79         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.79           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.58/0.79  thf('0', plain,
% 0.58/0.79      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.58/0.79         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.58/0.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.58/0.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.58/0.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.79  thf(d1_tarski, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.79         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('2', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.58/0.79      inference('simplify', [status(thm)], ['1'])).
% 0.58/0.79  thf(l35_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.79       ( r2_hidden @ A @ B ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X12 : $i, X14 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ (k1_tarski @ X12) @ X14) = (k1_xboole_0))
% 0.58/0.79          | ~ (r2_hidden @ X12 @ X14))),
% 0.58/0.79      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X4 @ X3)
% 0.58/0.79          | (r2_hidden @ X4 @ X1)
% 0.58/0.79          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.79         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['5'])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.58/0.79          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['4', '6'])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X4 @ X3)
% 0.58/0.79          | ~ (r2_hidden @ X4 @ X2)
% 0.58/0.79          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.79          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['9'])).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.58/0.79          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['8', '10'])).
% 0.58/0.79  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.79      inference('clc', [status(thm)], ['7', '11'])).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.58/0.79          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['0', '12'])).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.58/0.79          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['0', '12'])).
% 0.58/0.79  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.79      inference('clc', [status(thm)], ['7', '11'])).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.58/0.79          | ((X1) = (k1_xboole_0)))),
% 0.58/0.79      inference('demod', [status(thm)], ['13', '16'])).
% 0.58/0.79  thf(t66_zfmisc_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.58/0.79          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i]:
% 0.58/0.79        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.58/0.79             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('19', plain,
% 0.58/0.79      (![X6 : $i, X10 : $i]:
% 0.58/0.79         (((X10) = (k1_tarski @ X6))
% 0.58/0.79          | ((sk_C @ X10 @ X6) = (X6))
% 0.58/0.79          | (r2_hidden @ (sk_C @ X10 @ X6) @ X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.79          | (r2_hidden @ X0 @ X2)
% 0.58/0.79          | (r2_hidden @ X0 @ X3)
% 0.58/0.79          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.58/0.79          | (r2_hidden @ X0 @ X2)
% 0.58/0.79          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.79      inference('simplify', [status(thm)], ['20'])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         (((sk_C @ X0 @ X1) = (X1))
% 0.58/0.79          | ((X0) = (k1_tarski @ X1))
% 0.58/0.79          | (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 0.58/0.79          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['19', '21'])).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_C @ sk_A @ X0) @ k1_xboole_0)
% 0.58/0.79          | (r2_hidden @ (sk_C @ sk_A @ X0) @ (k1_tarski @ sk_B))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['18', '22'])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      (![X6 : $i, X9 : $i]:
% 0.58/0.79         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_C @ sk_A @ X0) = (X0))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | (r2_hidden @ (sk_C @ sk_A @ X0) @ k1_xboole_0)
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['23', '25'])).
% 0.58/0.79  thf('27', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.79      inference('clc', [status(thm)], ['7', '11'])).
% 0.58/0.79  thf('28', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_C @ sk_A @ X0) = (sk_B))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.79  thf('29', plain,
% 0.58/0.79      (![X6 : $i, X10 : $i]:
% 0.58/0.79         (((X10) = (k1_tarski @ X6))
% 0.58/0.79          | ((sk_C @ X10 @ X6) = (X6))
% 0.58/0.79          | (r2_hidden @ (sk_C @ X10 @ X6) @ X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('30', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((r2_hidden @ sk_B @ sk_A)
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (X0))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (X0))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['28', '29'])).
% 0.58/0.79  thf('31', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (X0))
% 0.58/0.79          | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.79      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.79  thf('32', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_C @ sk_A @ X0) = (sk_B))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((X0) != (sk_B))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) = (sk_B)))),
% 0.58/0.79      inference('eq_fact', [status(thm)], ['32'])).
% 0.58/0.79  thf('34', plain,
% 0.58/0.79      ((((sk_C @ sk_A @ sk_B) = (sk_B)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.58/0.79  thf('35', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('36', plain, (((sk_C @ sk_A @ sk_B) = (sk_B))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.58/0.79  thf('37', plain,
% 0.58/0.79      (![X6 : $i, X10 : $i]:
% 0.58/0.79         (((X10) = (k1_tarski @ X6))
% 0.58/0.79          | ((sk_C @ X10 @ X6) != (X6))
% 0.58/0.79          | ~ (r2_hidden @ (sk_C @ X10 @ X6) @ X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.58/0.79        | ((sk_C @ sk_A @ sk_B) != (sk_B))
% 0.58/0.79        | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.79  thf('39', plain, (((sk_C @ sk_A @ sk_B) = (sk_B))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.58/0.79  thf('40', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.58/0.79        | ((sk_B) != (sk_B))
% 0.58/0.79        | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.58/0.79      inference('demod', [status(thm)], ['38', '39'])).
% 0.58/0.79  thf('41', plain,
% 0.58/0.79      ((((sk_A) = (k1_tarski @ sk_B)) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.79      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.79  thf('42', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('43', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.58/0.79  thf('44', plain,
% 0.58/0.79      (![X0 : $i]: (((sk_C @ sk_A @ X0) = (X0)) | ((sk_A) = (k1_tarski @ X0)))),
% 0.58/0.79      inference('clc', [status(thm)], ['31', '43'])).
% 0.58/0.79  thf('45', plain,
% 0.58/0.79      (![X6 : $i, X10 : $i]:
% 0.58/0.79         (((X10) = (k1_tarski @ X6))
% 0.58/0.79          | ((sk_C @ X10 @ X6) != (X6))
% 0.58/0.79          | ~ (r2_hidden @ (sk_C @ X10 @ X6) @ X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('46', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X0 @ sk_A)
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ((sk_C @ sk_A @ X0) != (X0))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.79  thf('47', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_C @ sk_A @ X0) != (X0))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ X0))
% 0.58/0.79          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.58/0.79      inference('simplify', [status(thm)], ['46'])).
% 0.58/0.79  thf('48', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_A) = (k1_xboole_0))
% 0.58/0.79          | ((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ k1_xboole_0)))
% 0.58/0.79          | ((sk_C @ sk_A @ (sk_D @ sk_A @ X0 @ k1_xboole_0))
% 0.58/0.79              != (sk_D @ sk_A @ X0 @ k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['17', '47'])).
% 0.58/0.79  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('50', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ k1_xboole_0)))
% 0.58/0.79          | ((sk_C @ sk_A @ (sk_D @ sk_A @ X0 @ k1_xboole_0))
% 0.58/0.79              != (sk_D @ sk_A @ X0 @ k1_xboole_0)))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.58/0.79  thf('51', plain,
% 0.58/0.79      (![X0 : $i]: (((sk_C @ sk_A @ X0) = (X0)) | ((sk_A) = (k1_tarski @ X0)))),
% 0.58/0.79      inference('clc', [status(thm)], ['31', '43'])).
% 0.58/0.79  thf('52', plain,
% 0.58/0.79      (![X0 : $i]: ((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ k1_xboole_0)))),
% 0.58/0.79      inference('clc', [status(thm)], ['50', '51'])).
% 0.58/0.79  thf('53', plain,
% 0.58/0.79      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('54', plain,
% 0.58/0.79      (![X0 : $i]: ((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ k1_xboole_0)))),
% 0.58/0.79      inference('clc', [status(thm)], ['50', '51'])).
% 0.58/0.79  thf('55', plain,
% 0.58/0.79      (![X12 : $i, X13 : $i]:
% 0.58/0.79         ((r2_hidden @ X12 @ X13)
% 0.58/0.79          | ((k4_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.58/0.79  thf('56', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.58/0.79          | (r2_hidden @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.79  thf('57', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.79          | (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k1_tarski @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['53', '56'])).
% 0.58/0.79  thf('58', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k1_tarski @ sk_B))),
% 0.58/0.79      inference('simplify', [status(thm)], ['57'])).
% 0.58/0.79  thf('59', plain,
% 0.58/0.79      (![X6 : $i, X9 : $i]:
% 0.58/0.79         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.79  thf('60', plain, (![X0 : $i]: ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.79  thf('61', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.58/0.79      inference('demod', [status(thm)], ['52', '60'])).
% 0.58/0.79  thf('62', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('63', plain, ($false),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
