%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8KjdamksZJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:51 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 152 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  498 (1044 expanded)
%              Number of equality atoms :   41 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t95_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X21 ) @ X22 )
      | ( r2_hidden @ ( sk_C @ X22 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('45',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','47'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ X20 ) )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( sk_C @ X22 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('55',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8KjdamksZJ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 270 iterations in 0.116s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(t95_zfmisc_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.57       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i]:
% 0.38/0.57        ( ( r1_tarski @ A @ B ) =>
% 0.38/0.57          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t95_zfmisc_1])).
% 0.38/0.57  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t94_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.38/0.57       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i]:
% 0.38/0.57         ((r1_tarski @ (k3_tarski @ X21) @ X22)
% 0.38/0.57          | (r2_hidden @ (sk_C @ X22 @ X21) @ X21))),
% 0.38/0.57      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.38/0.57  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(l32_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X11 : $i, X13 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X11 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('4', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf(t48_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf(t36_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.38/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.57      inference('sup+', [status(thm)], ['7', '10'])).
% 0.38/0.57  thf('12', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B)),
% 0.38/0.57      inference('sup+', [status(thm)], ['6', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X11 : $i, X13 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X11 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B)
% 0.38/0.57         = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ k1_xboole_0)
% 0.38/0.57         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ k1_xboole_0)
% 0.38/0.57         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf(d5_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X6 @ X5)
% 0.38/0.57          | (r2_hidden @ X6 @ X3)
% 0.38/0.57          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.38/0.57         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X0 @ 
% 0.38/0.57             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ k1_xboole_0))
% 0.38/0.57          | (r2_hidden @ X0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['18', '22'])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('25', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.38/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X11 : $i, X13 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X11 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 0.38/0.57           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.57  thf('34', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.38/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X11 : $i, X13 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X11 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i]:
% 0.38/0.57         ((r1_tarski @ X11 @ X12)
% 0.38/0.57          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.57          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.57  thf('43', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X8 : $i, X10 : $i]:
% 0.38/0.57         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.38/0.57          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.57  thf('47', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['43', '46'])).
% 0.38/0.57  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '47'])).
% 0.38/0.57  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '47'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['23', '48', '49'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.38/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '50'])).
% 0.38/0.57  thf(l49_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         ((r1_tarski @ X19 @ (k3_tarski @ X20)) | ~ (r2_hidden @ X19 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.38/0.57          | (r1_tarski @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i]:
% 0.38/0.57         ((r1_tarski @ (k3_tarski @ X21) @ X22)
% 0.38/0.57          | ~ (r1_tarski @ (sk_C @ X22 @ X21) @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 0.38/0.57        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.57  thf('56', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.38/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.57  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
