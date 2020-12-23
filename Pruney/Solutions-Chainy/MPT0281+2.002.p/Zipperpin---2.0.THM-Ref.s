%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qUKbNQg5R

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:46 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   75 (  99 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  526 ( 754 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t82_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
        = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
     => ( r3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
          = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
       => ( r3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t82_zfmisc_1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X29 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    = ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('22',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('25',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r3_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r3_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qUKbNQg5R
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.92/2.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.92/2.10  % Solved by: fo/fo7.sh
% 1.92/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.92/2.10  % done 1507 iterations in 1.638s
% 1.92/2.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.92/2.10  % SZS output start Refutation
% 1.92/2.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.92/2.10  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 1.92/2.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.92/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.92/2.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.92/2.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.92/2.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.92/2.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.92/2.10  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.92/2.10  thf(sk_B_type, type, sk_B: $i).
% 1.92/2.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.92/2.10  thf(t82_zfmisc_1, conjecture,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 1.92/2.10         ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 1.92/2.10       ( r3_xboole_0 @ A @ B ) ))).
% 1.92/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.92/2.10    (~( ![A:$i,B:$i]:
% 1.92/2.10        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 1.92/2.10            ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 1.92/2.10          ( r3_xboole_0 @ A @ B ) ) )),
% 1.92/2.10    inference('cnf.neg', [status(esa)], [t82_zfmisc_1])).
% 1.92/2.10  thf('0', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf(d10_xboole_0, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.92/2.10  thf('1', plain,
% 1.92/2.10      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.92/2.10  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.92/2.10      inference('simplify', [status(thm)], ['1'])).
% 1.92/2.10  thf(d1_zfmisc_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.92/2.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.92/2.10  thf('3', plain,
% 1.92/2.10      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.92/2.10         (~ (r1_tarski @ X27 @ X28)
% 1.92/2.10          | (r2_hidden @ X27 @ X29)
% 1.92/2.10          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.92/2.10  thf('4', plain,
% 1.92/2.10      (![X27 : $i, X28 : $i]:
% 1.92/2.10         ((r2_hidden @ X27 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X27 @ X28))),
% 1.92/2.10      inference('simplify', [status(thm)], ['3'])).
% 1.92/2.10  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.92/2.10      inference('sup-', [status(thm)], ['2', '4'])).
% 1.92/2.10  thf('6', plain,
% 1.92/2.10      (((k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 1.92/2.10         = (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf(d1_tarski, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.92/2.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.92/2.10  thf('7', plain,
% 1.92/2.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.92/2.10         (((X20) != (X19))
% 1.92/2.10          | (r2_hidden @ X20 @ X21)
% 1.92/2.10          | ((X21) != (k1_tarski @ X19)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d1_tarski])).
% 1.92/2.10  thf('8', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_tarski @ X19))),
% 1.92/2.10      inference('simplify', [status(thm)], ['7'])).
% 1.92/2.10  thf(d5_xboole_0, axiom,
% 1.92/2.10    (![A:$i,B:$i,C:$i]:
% 1.92/2.10     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.92/2.10       ( ![D:$i]:
% 1.92/2.10         ( ( r2_hidden @ D @ C ) <=>
% 1.92/2.10           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.92/2.10  thf('9', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X0 @ X1)
% 1.92/2.10          | (r2_hidden @ X0 @ X2)
% 1.92/2.10          | (r2_hidden @ X0 @ X3)
% 1.92/2.10          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.92/2.10  thf('10', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.92/2.10          | (r2_hidden @ X0 @ X2)
% 1.92/2.10          | ~ (r2_hidden @ X0 @ X1))),
% 1.92/2.10      inference('simplify', [status(thm)], ['9'])).
% 1.92/2.10  thf('11', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((r2_hidden @ X0 @ X1)
% 1.92/2.10          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['8', '10'])).
% 1.92/2.10  thf('12', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.92/2.10          | (r2_hidden @ X0 @ X2)
% 1.92/2.10          | ~ (r2_hidden @ X0 @ X1))),
% 1.92/2.10      inference('simplify', [status(thm)], ['9'])).
% 1.92/2.10  thf('13', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         ((r2_hidden @ X1 @ X0)
% 1.92/2.10          | (r2_hidden @ X1 @ X2)
% 1.92/2.10          | (r2_hidden @ X1 @ 
% 1.92/2.10             (k4_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['11', '12'])).
% 1.92/2.10  thf(t41_xboole_1, axiom,
% 1.92/2.10    (![A:$i,B:$i,C:$i]:
% 1.92/2.10     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.92/2.10       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.92/2.10  thf('14', plain,
% 1.92/2.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.92/2.10           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.92/2.10      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.92/2.10  thf('15', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         ((r2_hidden @ X1 @ X0)
% 1.92/2.10          | (r2_hidden @ X1 @ X2)
% 1.92/2.10          | (r2_hidden @ X1 @ 
% 1.92/2.10             (k4_xboole_0 @ (k1_tarski @ X1) @ (k2_xboole_0 @ X0 @ X2))))),
% 1.92/2.10      inference('demod', [status(thm)], ['13', '14'])).
% 1.92/2.10  thf('16', plain,
% 1.92/2.10      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X4 @ X3)
% 1.92/2.10          | ~ (r2_hidden @ X4 @ X2)
% 1.92/2.10          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.92/2.10  thf('17', plain,
% 1.92/2.10      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X4 @ X2)
% 1.92/2.10          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.92/2.10      inference('simplify', [status(thm)], ['16'])).
% 1.92/2.10  thf('18', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         ((r2_hidden @ X2 @ X0)
% 1.92/2.10          | (r2_hidden @ X2 @ X1)
% 1.92/2.10          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['15', '17'])).
% 1.92/2.10  thf('19', plain,
% 1.92/2.10      (![X0 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))
% 1.92/2.10          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.92/2.10          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['6', '18'])).
% 1.92/2.10  thf('20', plain,
% 1.92/2.10      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))
% 1.92/2.10        | (r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['5', '19'])).
% 1.92/2.10  thf('21', plain,
% 1.92/2.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X30 @ X29)
% 1.92/2.10          | (r1_tarski @ X30 @ X28)
% 1.92/2.10          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.92/2.10  thf('22', plain,
% 1.92/2.10      (![X28 : $i, X30 : $i]:
% 1.92/2.10         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 1.92/2.10      inference('simplify', [status(thm)], ['21'])).
% 1.92/2.10  thf('23', plain,
% 1.92/2.10      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 1.92/2.10        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 1.92/2.10      inference('sup-', [status(thm)], ['20', '22'])).
% 1.92/2.10  thf('24', plain,
% 1.92/2.10      (![X28 : $i, X30 : $i]:
% 1.92/2.10         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 1.92/2.10      inference('simplify', [status(thm)], ['21'])).
% 1.92/2.10  thf('25', plain,
% 1.92/2.10      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 1.92/2.10        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 1.92/2.10      inference('sup-', [status(thm)], ['23', '24'])).
% 1.92/2.10  thf(commutativity_k2_tarski, axiom,
% 1.92/2.10    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.92/2.10  thf('26', plain,
% 1.92/2.10      (![X17 : $i, X18 : $i]:
% 1.92/2.10         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 1.92/2.10      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.92/2.10  thf(l51_zfmisc_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.92/2.10  thf('27', plain,
% 1.92/2.10      (![X32 : $i, X33 : $i]:
% 1.92/2.10         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 1.92/2.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.92/2.10  thf('28', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.92/2.10      inference('sup+', [status(thm)], ['26', '27'])).
% 1.92/2.10  thf('29', plain,
% 1.92/2.10      (![X32 : $i, X33 : $i]:
% 1.92/2.10         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 1.92/2.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.92/2.10  thf('30', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.92/2.10      inference('sup+', [status(thm)], ['28', '29'])).
% 1.92/2.10  thf(t7_xboole_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.92/2.10  thf('31', plain,
% 1.92/2.10      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.92/2.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.92/2.10  thf('32', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.92/2.10      inference('sup+', [status(thm)], ['30', '31'])).
% 1.92/2.10  thf('33', plain,
% 1.92/2.10      (![X6 : $i, X8 : $i]:
% 1.92/2.10         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.92/2.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.92/2.10  thf('34', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.92/2.10          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['32', '33'])).
% 1.92/2.10  thf('35', plain,
% 1.92/2.10      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 1.92/2.10        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_B)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['25', '34'])).
% 1.92/2.10  thf('36', plain,
% 1.92/2.10      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.92/2.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.92/2.10  thf('37', plain,
% 1.92/2.10      (![X6 : $i, X8 : $i]:
% 1.92/2.10         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.92/2.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.92/2.10  thf('38', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.92/2.10          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['36', '37'])).
% 1.92/2.10  thf('39', plain,
% 1.92/2.10      ((((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))
% 1.92/2.10        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['35', '38'])).
% 1.92/2.10  thf('40', plain,
% 1.92/2.10      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.92/2.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.92/2.10  thf(d9_xboole_0, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( r3_xboole_0 @ A @ B ) <=>
% 1.92/2.10       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 1.92/2.10  thf('41', plain,
% 1.92/2.10      (![X10 : $i, X11 : $i]:
% 1.92/2.10         ((r3_xboole_0 @ X10 @ X11) | ~ (r1_tarski @ X10 @ X11))),
% 1.92/2.10      inference('cnf', [status(esa)], [d9_xboole_0])).
% 1.92/2.10  thf('42', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.92/2.10      inference('sup-', [status(thm)], ['40', '41'])).
% 1.92/2.10  thf('43', plain,
% 1.92/2.10      (((r3_xboole_0 @ sk_A @ sk_B) | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 1.92/2.10      inference('sup+', [status(thm)], ['39', '42'])).
% 1.92/2.10  thf('44', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf('45', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.92/2.10      inference('clc', [status(thm)], ['43', '44'])).
% 1.92/2.10  thf('46', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.92/2.10      inference('sup+', [status(thm)], ['28', '29'])).
% 1.92/2.10  thf('47', plain,
% 1.92/2.10      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.92/2.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.92/2.10  thf('48', plain,
% 1.92/2.10      (![X10 : $i, X11 : $i]:
% 1.92/2.10         ((r3_xboole_0 @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 1.92/2.10      inference('cnf', [status(esa)], [d9_xboole_0])).
% 1.92/2.10  thf('49', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)),
% 1.92/2.10      inference('sup-', [status(thm)], ['47', '48'])).
% 1.92/2.10  thf('50', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)),
% 1.92/2.10      inference('sup+', [status(thm)], ['46', '49'])).
% 1.92/2.10  thf('51', plain, ((r3_xboole_0 @ sk_A @ sk_B)),
% 1.92/2.10      inference('sup+', [status(thm)], ['45', '50'])).
% 1.92/2.10  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 1.92/2.10  
% 1.92/2.10  % SZS output end Refutation
% 1.92/2.10  
% 1.92/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
