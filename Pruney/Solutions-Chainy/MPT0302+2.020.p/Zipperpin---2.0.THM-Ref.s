%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWUFfgy5m6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:08 EST 2020

% Result     : Theorem 4.44s
% Output     : Refutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 150 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  568 (1295 expanded)
%              Number of equality atoms :   28 ( 100 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X30 @ X32 ) @ ( k2_zfmisc_1 @ X31 @ X34 ) )
      | ~ ( r2_hidden @ X32 @ X34 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ X32 ) @ ( k2_zfmisc_1 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( sk_B = X0 )
      | ( r2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r1_tarski @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('25',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X10 ) )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ X32 ) @ ( k2_zfmisc_1 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['29','55'])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('58',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWUFfgy5m6
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.44/4.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.44/4.66  % Solved by: fo/fo7.sh
% 4.44/4.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.44/4.66  % done 2649 iterations in 4.196s
% 4.44/4.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.44/4.66  % SZS output start Refutation
% 4.44/4.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.44/4.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.44/4.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.44/4.66  thf(sk_A_type, type, sk_A: $i).
% 4.44/4.66  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 4.44/4.66  thf(sk_B_type, type, sk_B: $i).
% 4.44/4.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.44/4.66  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.44/4.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.44/4.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.44/4.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.44/4.66  thf(d3_tarski, axiom,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ( r1_tarski @ A @ B ) <=>
% 4.44/4.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.44/4.66  thf('0', plain,
% 4.44/4.66      (![X1 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf('1', plain,
% 4.44/4.66      (![X1 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf(l54_zfmisc_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i,D:$i]:
% 4.44/4.66     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 4.44/4.66       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 4.44/4.66  thf('2', plain,
% 4.44/4.66      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 4.44/4.66         ((r2_hidden @ (k4_tarski @ X30 @ X32) @ (k2_zfmisc_1 @ X31 @ X34))
% 4.44/4.66          | ~ (r2_hidden @ X32 @ X34)
% 4.44/4.66          | ~ (r2_hidden @ X30 @ X31))),
% 4.44/4.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.44/4.66  thf('3', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X0 @ X1)
% 4.44/4.66          | ~ (r2_hidden @ X3 @ X2)
% 4.44/4.66          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 4.44/4.66             (k2_zfmisc_1 @ X2 @ X0)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['1', '2'])).
% 4.44/4.66  thf('4', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X0 @ X1)
% 4.44/4.66          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 4.44/4.66             (k2_zfmisc_1 @ X0 @ X2))
% 4.44/4.66          | (r1_tarski @ X2 @ X3))),
% 4.44/4.66      inference('sup-', [status(thm)], ['0', '3'])).
% 4.44/4.66  thf(t114_zfmisc_1, conjecture,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 4.44/4.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.44/4.66         ( ( A ) = ( B ) ) ) ))).
% 4.44/4.66  thf(zf_stmt_0, negated_conjecture,
% 4.44/4.66    (~( ![A:$i,B:$i]:
% 4.44/4.66        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 4.44/4.66          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.44/4.66            ( ( A ) = ( B ) ) ) ) )),
% 4.44/4.66    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 4.44/4.66  thf('5', plain,
% 4.44/4.66      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('6', plain,
% 4.44/4.66      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.44/4.66         ((r2_hidden @ X30 @ X31)
% 4.44/4.66          | ~ (r2_hidden @ (k4_tarski @ X30 @ X32) @ (k2_zfmisc_1 @ X31 @ X33)))),
% 4.44/4.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.44/4.66  thf('7', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 4.44/4.66          | (r2_hidden @ X1 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['5', '6'])).
% 4.44/4.66  thf('8', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         ((r1_tarski @ sk_B @ X0)
% 4.44/4.66          | (r1_tarski @ sk_A @ X1)
% 4.44/4.66          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['4', '7'])).
% 4.44/4.66  thf('9', plain,
% 4.44/4.66      (![X1 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf('10', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((r1_tarski @ sk_A @ sk_B)
% 4.44/4.66          | (r1_tarski @ sk_B @ X0)
% 4.44/4.66          | (r1_tarski @ sk_A @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['8', '9'])).
% 4.44/4.66  thf('11', plain,
% 4.44/4.66      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ sk_B))),
% 4.44/4.66      inference('simplify', [status(thm)], ['10'])).
% 4.44/4.66  thf(d8_xboole_0, axiom,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ( r2_xboole_0 @ A @ B ) <=>
% 4.44/4.66       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 4.44/4.66  thf('12', plain,
% 4.44/4.66      (![X4 : $i, X6 : $i]:
% 4.44/4.66         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 4.44/4.66      inference('cnf', [status(esa)], [d8_xboole_0])).
% 4.44/4.66  thf('13', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((r1_tarski @ sk_A @ sk_B)
% 4.44/4.66          | ((sk_B) = (X0))
% 4.44/4.66          | (r2_xboole_0 @ sk_B @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['11', '12'])).
% 4.44/4.66  thf(t6_xboole_0, axiom,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 4.44/4.66          ( ![C:$i]:
% 4.44/4.66            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 4.44/4.66  thf('14', plain,
% 4.44/4.66      (![X11 : $i, X12 : $i]:
% 4.44/4.66         (~ (r2_xboole_0 @ X11 @ X12)
% 4.44/4.66          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X12))),
% 4.44/4.66      inference('cnf', [status(esa)], [t6_xboole_0])).
% 4.44/4.66  thf('15', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (((sk_B) = (X0))
% 4.44/4.66          | (r1_tarski @ sk_A @ sk_B)
% 4.44/4.66          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['13', '14'])).
% 4.44/4.66  thf(t5_boole, axiom,
% 4.44/4.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.44/4.66  thf('16', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 4.44/4.66      inference('cnf', [status(esa)], [t5_boole])).
% 4.44/4.66  thf(t1_xboole_0, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i]:
% 4.44/4.66     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 4.44/4.66       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 4.44/4.66  thf('17', plain,
% 4.44/4.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.44/4.66         (~ (r2_hidden @ X7 @ X8)
% 4.44/4.66          | ~ (r2_hidden @ X7 @ X9)
% 4.44/4.66          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 4.44/4.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.44/4.66  thf('18', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (r2_hidden @ X1 @ X0)
% 4.44/4.66          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 4.44/4.66          | ~ (r2_hidden @ X1 @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['16', '17'])).
% 4.44/4.66  thf('19', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 4.44/4.66      inference('simplify', [status(thm)], ['18'])).
% 4.44/4.66  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.44/4.66      inference('condensation', [status(thm)], ['19'])).
% 4.44/4.66  thf('21', plain, (((r1_tarski @ sk_A @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['15', '20'])).
% 4.44/4.66  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('23', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.44/4.66      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 4.44/4.66  thf('24', plain,
% 4.44/4.66      (![X4 : $i, X6 : $i]:
% 4.44/4.66         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 4.44/4.66      inference('cnf', [status(esa)], [d8_xboole_0])).
% 4.44/4.66  thf('25', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['23', '24'])).
% 4.44/4.66  thf('26', plain, (((sk_A) != (sk_B))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('27', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 4.44/4.66      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 4.44/4.66  thf('28', plain,
% 4.44/4.66      (![X11 : $i, X12 : $i]:
% 4.44/4.66         (~ (r2_xboole_0 @ X11 @ X12)
% 4.44/4.66          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X12))),
% 4.44/4.66      inference('cnf', [status(esa)], [t6_xboole_0])).
% 4.44/4.66  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['27', '28'])).
% 4.44/4.66  thf('30', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 4.44/4.66      inference('cnf', [status(esa)], [t5_boole])).
% 4.44/4.66  thf('31', plain,
% 4.44/4.66      (![X1 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf('32', plain,
% 4.44/4.66      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.44/4.66         ((r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X10))
% 4.44/4.66          | (r2_hidden @ X7 @ X8)
% 4.44/4.66          | ~ (r2_hidden @ X7 @ X10))),
% 4.44/4.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.44/4.66  thf('33', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.44/4.66         ((r1_tarski @ X0 @ X1)
% 4.44/4.66          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 4.44/4.66          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['31', '32'])).
% 4.44/4.66  thf('34', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         ((r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0)
% 4.44/4.66          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0)
% 4.44/4.66          | (r1_tarski @ k1_xboole_0 @ X1))),
% 4.44/4.66      inference('sup+', [status(thm)], ['30', '33'])).
% 4.44/4.66  thf('35', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         ((r1_tarski @ k1_xboole_0 @ X1)
% 4.44/4.66          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0))),
% 4.44/4.66      inference('simplify', [status(thm)], ['34'])).
% 4.44/4.66  thf('36', plain,
% 4.44/4.66      (![X1 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf('37', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((r1_tarski @ k1_xboole_0 @ X0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['35', '36'])).
% 4.44/4.66  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.44/4.66      inference('simplify', [status(thm)], ['37'])).
% 4.44/4.66  thf('39', plain,
% 4.44/4.66      (![X4 : $i, X6 : $i]:
% 4.44/4.66         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 4.44/4.66      inference('cnf', [status(esa)], [d8_xboole_0])).
% 4.44/4.66  thf('40', plain,
% 4.44/4.66      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['38', '39'])).
% 4.44/4.66  thf('41', plain,
% 4.44/4.66      (![X11 : $i, X12 : $i]:
% 4.44/4.66         (~ (r2_xboole_0 @ X11 @ X12)
% 4.44/4.66          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X12))),
% 4.44/4.66      inference('cnf', [status(esa)], [t6_xboole_0])).
% 4.44/4.66  thf('42', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (((k1_xboole_0) = (X0))
% 4.44/4.66          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['40', '41'])).
% 4.44/4.66  thf('43', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X0 @ X1)
% 4.44/4.66          | ~ (r2_hidden @ X3 @ X2)
% 4.44/4.66          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 4.44/4.66             (k2_zfmisc_1 @ X2 @ X0)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['1', '2'])).
% 4.44/4.66  thf('44', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.44/4.66         (((k1_xboole_0) = (X0))
% 4.44/4.66          | (r2_hidden @ 
% 4.44/4.66             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 4.44/4.66             (k2_zfmisc_1 @ X0 @ X1))
% 4.44/4.66          | (r1_tarski @ X1 @ X2))),
% 4.44/4.66      inference('sup-', [status(thm)], ['42', '43'])).
% 4.44/4.66  thf('45', plain,
% 4.44/4.66      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('46', plain,
% 4.44/4.66      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.44/4.66         ((r2_hidden @ X32 @ X33)
% 4.44/4.66          | ~ (r2_hidden @ (k4_tarski @ X30 @ X32) @ (k2_zfmisc_1 @ X31 @ X33)))),
% 4.44/4.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.44/4.66  thf('47', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 4.44/4.66          | (r2_hidden @ X0 @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['45', '46'])).
% 4.44/4.66  thf('48', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((r1_tarski @ sk_B @ X0)
% 4.44/4.66          | ((k1_xboole_0) = (sk_A))
% 4.44/4.66          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['44', '47'])).
% 4.44/4.66  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('50', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 4.44/4.66      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 4.44/4.66  thf('51', plain,
% 4.44/4.66      (![X1 : $i, X3 : $i]:
% 4.44/4.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf('52', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['50', '51'])).
% 4.44/4.66  thf('53', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.44/4.66      inference('simplify', [status(thm)], ['52'])).
% 4.44/4.66  thf('54', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.44/4.66         (~ (r2_hidden @ X0 @ X1)
% 4.44/4.66          | (r2_hidden @ X0 @ X2)
% 4.44/4.66          | ~ (r1_tarski @ X1 @ X2))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_tarski])).
% 4.44/4.66  thf('55', plain,
% 4.44/4.66      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['53', '54'])).
% 4.44/4.66  thf('56', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 4.44/4.66      inference('sup-', [status(thm)], ['29', '55'])).
% 4.44/4.66  thf('57', plain,
% 4.44/4.66      (![X11 : $i, X12 : $i]:
% 4.44/4.66         (~ (r2_xboole_0 @ X11 @ X12)
% 4.44/4.66          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X11))),
% 4.44/4.66      inference('cnf', [status(esa)], [t6_xboole_0])).
% 4.44/4.66  thf('58', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['56', '57'])).
% 4.44/4.66  thf('59', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 4.44/4.66      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 4.44/4.66  thf('60', plain, ($false), inference('demod', [status(thm)], ['58', '59'])).
% 4.44/4.66  
% 4.44/4.66  % SZS output end Refutation
% 4.44/4.66  
% 4.44/4.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
