%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uNtbb2QIj0

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 232 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  473 (1332 expanded)
%              Number of equality atoms :   49 ( 157 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X20 ) @ ( k3_tarski @ X21 ) )
      | ~ ( r1_setfam_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('4',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k3_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( X4
        = ( k3_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(demod,[status(thm)],['0','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_D @ X15 @ X16 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ~ ( r1_setfam_1 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_tarski @ sk_A ) )
      = X8 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('39',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ sk_A ) @ X11 )
      = ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X20 ) @ ( k3_tarski @ X21 ) )
      | ~ ( r1_setfam_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('46',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('50',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_tarski @ sk_A ) )
      = X8 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','41','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','56'])).

thf('58',plain,
    ( sk_A
    = ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( k1_xboole_0
    = ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('61',plain,(
    sk_A
 != ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uNtbb2QIj0
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 277 iterations in 0.074s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.54  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(t7_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.54  thf(t21_setfam_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.21/0.54  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t18_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_setfam_1 @ A @ B ) =>
% 0.21/0.54       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         ((r1_tarski @ (k3_tarski @ X20) @ (k3_tarski @ X21))
% 0.21/0.54          | ~ (r1_setfam_1 @ X20 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.54  thf('4', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.54  thf('5', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf(t28_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((k3_xboole_0 @ (k3_tarski @ sk_A) @ k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf(t2_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('9', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X4 : $i]:
% 0.21/0.54         (((X4) = (k3_tarski @ sk_A)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.54  thf(t3_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.54  thf('11', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf(t48_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i]: (r1_setfam_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf(d2_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.54              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_D @ X15 @ X16) @ X16)
% 0.21/0.54          | ~ (r2_hidden @ X15 @ X17)
% 0.21/0.54          | ~ (r1_setfam_1 @ X17 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ sk_A)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X1 @ (k4_xboole_0 @ X0 @ X0)) @ 
% 0.21/0.54             (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('21', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf('24', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X8 : $i]: ((k4_xboole_0 @ X8 @ (k3_tarski @ sk_A)) = (X8))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf('30', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X0 @ X0)
% 0.21/0.54           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['30', '33'])).
% 0.21/0.54  thf(t4_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.21/0.54          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ (k3_tarski @ sk_A))
% 0.21/0.54          | ~ (r1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.21/0.54               (k4_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '36'])).
% 0.21/0.54  thf(t4_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.54  thf('39', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('40', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X11 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ (k3_tarski @ sk_A) @ X11) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i]: (r1_setfam_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         ((r1_tarski @ (k3_tarski @ X20) @ (k3_tarski @ X21))
% 0.21/0.54          | ~ (r1_setfam_1 @ X20 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_tarski @ (k3_tarski @ sk_A) @ 
% 0.21/0.54          (k3_tarski @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('46', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]: ((k3_tarski @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '47'])).
% 0.21/0.54  thf('49', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('50', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf(t85_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X12 @ X13)
% 0.21/0.54          | (r1_xboole_0 @ X12 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.21/0.54          (k4_xboole_0 @ X0 @ (k3_tarski @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X8 : $i]: ((k4_xboole_0 @ X8 @ (k3_tarski @ sk_A)) = (X8))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ (k3_tarski @ sk_A) @ X0)),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '41', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '55'])).
% 0.21/0.54  thf('57', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['19', '56'])).
% 0.21/0.54  thf('58', plain, (((sk_A) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '57'])).
% 0.21/0.54  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain, (((k1_xboole_0) = (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('61', plain, (((sk_A) != (k3_tarski @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf('62', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
