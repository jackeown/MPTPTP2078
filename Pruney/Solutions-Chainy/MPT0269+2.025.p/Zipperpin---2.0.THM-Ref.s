%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.me0IrGsbQy

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:05 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 454 expanded)
%              Number of leaves         :   29 ( 164 expanded)
%              Depth                    :   18
%              Number of atoms          :  554 (3232 expanded)
%              Number of equality atoms :   73 ( 456 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('13',plain,(
    ! [X58: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X58 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','33','34'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('47',plain,(
    ! [X53: $i,X55: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X53 ) @ X55 )
      | ~ ( r2_hidden @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('53',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['42','44'])).

thf('54',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.me0IrGsbQy
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 424 iterations in 0.162s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(t7_xboole_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.62  thf(t66_zfmisc_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.43/0.62          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.43/0.62             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t95_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k3_xboole_0 @ A @ B ) =
% 0.43/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X18 : $i, X19 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X18 @ X19)
% 0.43/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.43/0.62              (k2_xboole_0 @ X18 @ X19)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.43/0.62  thf(t91_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.43/0.62           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X18 : $i, X19 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X18 @ X19)
% 0.43/0.62           = (k5_xboole_0 @ X18 @ 
% 0.43/0.62              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 0.43/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf(t92_xboole_1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.62  thf('5', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.43/0.62           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X18 : $i, X19 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X18 @ X19)
% 0.43/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.43/0.62              (k2_xboole_0 @ X18 @ X19)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X0 @ X0)
% 0.43/0.62           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.43/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.62  thf('11', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.62  thf(t69_enumset1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf(t31_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.43/0.62  thf('13', plain, (![X58 : $i]: ((k3_tarski @ (k1_tarski @ X58)) = (X58))),
% 0.43/0.62      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.43/0.62  thf('14', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf(l51_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X56 : $i, X57 : $i]:
% 0.43/0.62         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.43/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.62  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf('17', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11', '16'])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.43/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['4', '18'])).
% 0.43/0.62  thf(t100_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X9 @ X10)
% 0.43/0.62           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.43/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '17'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X1 @ X0)
% 0.43/0.62           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.43/0.62         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['1', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.43/0.62           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.62  thf('26', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.43/0.62           = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '17'])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.43/0.62           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf(t5_boole, axiom,
% 0.43/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.62  thf('30', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.43/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '17'])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11', '16'])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '33', '34'])).
% 0.43/0.62  thf(t7_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.62  thf('37', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf(d3_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.62          | (r2_hidden @ X0 @ X2)
% 0.43/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      ((((sk_A) = (k1_xboole_0))
% 0.43/0.62        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '39'])).
% 0.43/0.62  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('42', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.43/0.62  thf(d1_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X23 @ X22)
% 0.43/0.62          | ((X23) = (X20))
% 0.43/0.62          | ((X22) != (k1_tarski @ X20)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X20 : $i, X23 : $i]:
% 0.43/0.62         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.62  thf('45', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['42', '44'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.62  thf(l1_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X53 : $i, X55 : $i]:
% 0.43/0.62         ((r1_tarski @ (k1_tarski @ X53) @ X55) | ~ (r2_hidden @ X53 @ X55))),
% 0.43/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.62  thf(d10_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X6 : $i, X8 : $i]:
% 0.43/0.62         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k1_xboole_0))
% 0.43/0.62          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.43/0.62          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))
% 0.43/0.62        | ((sk_A) = (k1_tarski @ (sk_B @ sk_A)))
% 0.43/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '50'])).
% 0.43/0.62  thf('52', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf('53', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['42', '44'])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      ((((sk_A) = (k1_tarski @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.43/0.62  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('56', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('57', plain, ($false),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
