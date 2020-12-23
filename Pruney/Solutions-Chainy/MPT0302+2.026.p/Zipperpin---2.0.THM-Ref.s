%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBotOYl48A

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:08 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 154 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  539 (1342 expanded)
%              Number of equality atoms :   32 ( 114 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

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
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r1_tarski @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

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
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('53',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBotOYl48A
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 3.97/4.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.97/4.20  % Solved by: fo/fo7.sh
% 3.97/4.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.97/4.20  % done 3561 iterations in 3.749s
% 3.97/4.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.97/4.20  % SZS output start Refutation
% 3.97/4.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.97/4.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.97/4.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.97/4.20  thf(sk_A_type, type, sk_A: $i).
% 3.97/4.20  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.97/4.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.97/4.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.97/4.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.97/4.20  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.97/4.20  thf(sk_B_type, type, sk_B: $i).
% 3.97/4.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.97/4.20  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 3.97/4.20  thf(d3_tarski, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( r1_tarski @ A @ B ) <=>
% 3.97/4.20       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.97/4.20  thf('0', plain,
% 3.97/4.20      (![X1 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf('1', plain,
% 3.97/4.20      (![X1 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf(l54_zfmisc_1, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i,D:$i]:
% 3.97/4.20     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 3.97/4.20       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 3.97/4.20  thf('2', plain,
% 3.97/4.20      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 3.97/4.20         ((r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X20))
% 3.97/4.20          | ~ (r2_hidden @ X18 @ X20)
% 3.97/4.20          | ~ (r2_hidden @ X16 @ X17))),
% 3.97/4.20      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.97/4.20  thf('3', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X0 @ X1)
% 3.97/4.20          | ~ (r2_hidden @ X3 @ X2)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 3.97/4.20             (k2_zfmisc_1 @ X2 @ X0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['1', '2'])).
% 3.97/4.20  thf('4', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X0 @ X1)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 3.97/4.20             (k2_zfmisc_1 @ X0 @ X2))
% 3.97/4.20          | (r1_tarski @ X2 @ X3))),
% 3.97/4.20      inference('sup-', [status(thm)], ['0', '3'])).
% 3.97/4.20  thf(t114_zfmisc_1, conjecture,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 3.97/4.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.97/4.20         ( ( A ) = ( B ) ) ) ))).
% 3.97/4.20  thf(zf_stmt_0, negated_conjecture,
% 3.97/4.20    (~( ![A:$i,B:$i]:
% 3.97/4.20        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 3.97/4.20          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.97/4.20            ( ( A ) = ( B ) ) ) ) )),
% 3.97/4.20    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 3.97/4.20  thf('5', plain,
% 3.97/4.20      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf('6', plain,
% 3.97/4.20      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.97/4.20         ((r2_hidden @ X16 @ X17)
% 3.97/4.20          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 3.97/4.20      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.97/4.20  thf('7', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.97/4.20          | (r2_hidden @ X1 @ sk_B))),
% 3.97/4.20      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.20  thf('8', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         ((r1_tarski @ sk_B @ X0)
% 3.97/4.20          | (r1_tarski @ sk_A @ X1)
% 3.97/4.20          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 3.97/4.20      inference('sup-', [status(thm)], ['4', '7'])).
% 3.97/4.20  thf('9', plain,
% 3.97/4.20      (![X1 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf('10', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         ((r1_tarski @ sk_A @ sk_B)
% 3.97/4.20          | (r1_tarski @ sk_B @ X0)
% 3.97/4.20          | (r1_tarski @ sk_A @ sk_B))),
% 3.97/4.20      inference('sup-', [status(thm)], ['8', '9'])).
% 3.97/4.20  thf('11', plain,
% 3.97/4.20      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ sk_B))),
% 3.97/4.20      inference('simplify', [status(thm)], ['10'])).
% 3.97/4.20  thf(d8_xboole_0, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( r2_xboole_0 @ A @ B ) <=>
% 3.97/4.20       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 3.97/4.20  thf('12', plain,
% 3.97/4.20      (![X10 : $i, X12 : $i]:
% 3.97/4.20         ((r2_xboole_0 @ X10 @ X12)
% 3.97/4.20          | ((X10) = (X12))
% 3.97/4.20          | ~ (r1_tarski @ X10 @ X12))),
% 3.97/4.20      inference('cnf', [status(esa)], [d8_xboole_0])).
% 3.97/4.20  thf('13', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         ((r1_tarski @ sk_A @ sk_B)
% 3.97/4.20          | ((sk_B) = (X0))
% 3.97/4.20          | (r2_xboole_0 @ sk_B @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['11', '12'])).
% 3.97/4.20  thf(t6_xboole_0, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 3.97/4.20          ( ![C:$i]:
% 3.97/4.20            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 3.97/4.20  thf('14', plain,
% 3.97/4.20      (![X13 : $i, X14 : $i]:
% 3.97/4.20         (~ (r2_xboole_0 @ X13 @ X14)
% 3.97/4.20          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X14))),
% 3.97/4.20      inference('cnf', [status(esa)], [t6_xboole_0])).
% 3.97/4.20  thf('15', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         (((sk_B) = (X0))
% 3.97/4.20          | (r1_tarski @ sk_A @ sk_B)
% 3.97/4.20          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['13', '14'])).
% 3.97/4.20  thf(t3_boole, axiom,
% 3.97/4.20    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.97/4.20  thf('16', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 3.97/4.20      inference('cnf', [status(esa)], [t3_boole])).
% 3.97/4.20  thf(d5_xboole_0, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.97/4.20       ( ![D:$i]:
% 3.97/4.20         ( ( r2_hidden @ D @ C ) <=>
% 3.97/4.20           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.97/4.20  thf('17', plain,
% 3.97/4.20      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X8 @ X7)
% 3.97/4.20          | ~ (r2_hidden @ X8 @ X6)
% 3.97/4.20          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 3.97/4.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.97/4.20  thf('18', plain,
% 3.97/4.20      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X8 @ X6)
% 3.97/4.20          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 3.97/4.20      inference('simplify', [status(thm)], ['17'])).
% 3.97/4.20  thf('19', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['16', '18'])).
% 3.97/4.20  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.97/4.20      inference('condensation', [status(thm)], ['19'])).
% 3.97/4.20  thf('21', plain, (((r1_tarski @ sk_A @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['15', '20'])).
% 3.97/4.20  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf('23', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.97/4.20      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 3.97/4.20  thf('24', plain,
% 3.97/4.20      (![X10 : $i, X12 : $i]:
% 3.97/4.20         ((r2_xboole_0 @ X10 @ X12)
% 3.97/4.20          | ((X10) = (X12))
% 3.97/4.20          | ~ (r1_tarski @ X10 @ X12))),
% 3.97/4.20      inference('cnf', [status(esa)], [d8_xboole_0])).
% 3.97/4.20  thf('25', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 3.97/4.20      inference('sup-', [status(thm)], ['23', '24'])).
% 3.97/4.20  thf('26', plain, (((sk_A) != (sk_B))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf('27', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 3.97/4.20      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 3.97/4.20  thf('28', plain,
% 3.97/4.20      (![X13 : $i, X14 : $i]:
% 3.97/4.20         (~ (r2_xboole_0 @ X13 @ X14)
% 3.97/4.20          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X14))),
% 3.97/4.20      inference('cnf', [status(esa)], [t6_xboole_0])).
% 3.97/4.20  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 3.97/4.20      inference('sup-', [status(thm)], ['27', '28'])).
% 3.97/4.20  thf('30', plain,
% 3.97/4.20      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.97/4.20         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 3.97/4.20          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.97/4.20          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.97/4.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.97/4.20  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.97/4.20      inference('condensation', [status(thm)], ['19'])).
% 3.97/4.20  thf('32', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 3.97/4.20          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['30', '31'])).
% 3.97/4.20  thf('33', plain,
% 3.97/4.20      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.97/4.20         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 3.97/4.20          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.97/4.20          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.97/4.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.97/4.20  thf('34', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.97/4.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.97/4.20      inference('eq_fact', [status(thm)], ['33'])).
% 3.97/4.20  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.97/4.20      inference('condensation', [status(thm)], ['19'])).
% 3.97/4.20  thf('36', plain,
% 3.97/4.20      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['34', '35'])).
% 3.97/4.20  thf('37', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 3.97/4.20          | ((X1) = (k1_xboole_0)))),
% 3.97/4.20      inference('demod', [status(thm)], ['32', '36'])).
% 3.97/4.20  thf('38', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X0 @ X1)
% 3.97/4.20          | ~ (r2_hidden @ X3 @ X2)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 3.97/4.20             (k2_zfmisc_1 @ X2 @ X0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['1', '2'])).
% 3.97/4.20  thf('39', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.97/4.20         (((X0) = (k1_xboole_0))
% 3.97/4.20          | (r2_hidden @ 
% 3.97/4.20             (k4_tarski @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ (sk_C @ X3 @ X2)) @ 
% 3.97/4.20             (k2_zfmisc_1 @ X0 @ X2))
% 3.97/4.20          | (r1_tarski @ X2 @ X3))),
% 3.97/4.20      inference('sup-', [status(thm)], ['37', '38'])).
% 3.97/4.20  thf('40', plain,
% 3.97/4.20      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf('41', plain,
% 3.97/4.20      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.97/4.20         ((r2_hidden @ X18 @ X19)
% 3.97/4.20          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 3.97/4.20      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.97/4.20  thf('42', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.97/4.20          | (r2_hidden @ X0 @ sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['40', '41'])).
% 3.97/4.20  thf('43', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         ((r1_tarski @ sk_B @ X0)
% 3.97/4.20          | ((sk_A) = (k1_xboole_0))
% 3.97/4.20          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['39', '42'])).
% 3.97/4.20  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf('45', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 3.97/4.20      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 3.97/4.20  thf('46', plain,
% 3.97/4.20      (![X1 : $i, X3 : $i]:
% 3.97/4.20         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf('47', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['45', '46'])).
% 3.97/4.20  thf('48', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.97/4.20      inference('simplify', [status(thm)], ['47'])).
% 3.97/4.20  thf('49', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X0 @ X1)
% 3.97/4.20          | (r2_hidden @ X0 @ X2)
% 3.97/4.20          | ~ (r1_tarski @ X1 @ X2))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf('50', plain,
% 3.97/4.20      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 3.97/4.20      inference('sup-', [status(thm)], ['48', '49'])).
% 3.97/4.20  thf('51', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 3.97/4.20      inference('sup-', [status(thm)], ['29', '50'])).
% 3.97/4.20  thf('52', plain,
% 3.97/4.20      (![X13 : $i, X14 : $i]:
% 3.97/4.20         (~ (r2_xboole_0 @ X13 @ X14)
% 3.97/4.20          | ~ (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X13))),
% 3.97/4.20      inference('cnf', [status(esa)], [t6_xboole_0])).
% 3.97/4.20  thf('53', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 3.97/4.20      inference('sup-', [status(thm)], ['51', '52'])).
% 3.97/4.20  thf('54', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 3.97/4.20      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 3.97/4.20  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 3.97/4.20  
% 3.97/4.20  % SZS output end Refutation
% 3.97/4.20  
% 3.97/4.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
