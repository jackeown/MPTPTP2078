%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xbWopfDeJW

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:32 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 128 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  466 ( 928 expanded)
%              Number of equality atoms :   42 (  87 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X40 @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('29',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['0','38'])).

thf('40',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != sk_B ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xbWopfDeJW
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.69/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.69/1.86  % Solved by: fo/fo7.sh
% 1.69/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.69/1.86  % done 2703 iterations in 1.426s
% 1.69/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.69/1.86  % SZS output start Refutation
% 1.69/1.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.69/1.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.69/1.86  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.69/1.86  thf(sk_B_type, type, sk_B: $i).
% 1.69/1.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.69/1.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.69/1.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.69/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.69/1.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.69/1.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.69/1.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.69/1.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.69/1.86  thf(t39_xboole_1, axiom,
% 1.69/1.86    (![A:$i,B:$i]:
% 1.69/1.86     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.69/1.86  thf('0', plain,
% 1.69/1.86      (![X18 : $i, X19 : $i]:
% 1.69/1.86         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 1.69/1.86           = (k2_xboole_0 @ X18 @ X19))),
% 1.69/1.86      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.69/1.86  thf(t48_zfmisc_1, conjecture,
% 1.69/1.86    (![A:$i,B:$i,C:$i]:
% 1.69/1.86     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.69/1.86       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 1.69/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.69/1.86    (~( ![A:$i,B:$i,C:$i]:
% 1.69/1.86        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.69/1.86          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 1.69/1.86    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 1.69/1.86  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 1.69/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.86  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.69/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.86  thf(t38_zfmisc_1, axiom,
% 1.69/1.86    (![A:$i,B:$i,C:$i]:
% 1.69/1.86     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.69/1.86       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.69/1.86  thf('3', plain,
% 1.69/1.86      (![X40 : $i, X42 : $i, X43 : $i]:
% 1.69/1.86         ((r1_tarski @ (k2_tarski @ X40 @ X42) @ X43)
% 1.69/1.86          | ~ (r2_hidden @ X42 @ X43)
% 1.69/1.86          | ~ (r2_hidden @ X40 @ X43))),
% 1.69/1.86      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.69/1.86  thf('4', plain,
% 1.69/1.86      (![X0 : $i]:
% 1.69/1.86         (~ (r2_hidden @ X0 @ sk_B)
% 1.69/1.86          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 1.69/1.86      inference('sup-', [status(thm)], ['2', '3'])).
% 1.69/1.86  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_A) @ sk_B)),
% 1.69/1.86      inference('sup-', [status(thm)], ['1', '4'])).
% 1.69/1.86  thf(commutativity_k2_tarski, axiom,
% 1.69/1.86    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.69/1.86  thf('6', plain,
% 1.69/1.86      (![X27 : $i, X28 : $i]:
% 1.69/1.86         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 1.69/1.86      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.69/1.86  thf('7', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)),
% 1.69/1.86      inference('demod', [status(thm)], ['5', '6'])).
% 1.69/1.86  thf(t28_xboole_1, axiom,
% 1.69/1.86    (![A:$i,B:$i]:
% 1.69/1.86     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.69/1.86  thf('8', plain,
% 1.69/1.86      (![X16 : $i, X17 : $i]:
% 1.69/1.86         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.69/1.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.69/1.86  thf('9', plain,
% 1.69/1.86      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 1.69/1.86         = (k2_tarski @ sk_A @ sk_C_1))),
% 1.69/1.86      inference('sup-', [status(thm)], ['7', '8'])).
% 1.69/1.86  thf(t100_xboole_1, axiom,
% 1.69/1.86    (![A:$i,B:$i]:
% 1.69/1.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.69/1.86  thf('10', plain,
% 1.69/1.86      (![X14 : $i, X15 : $i]:
% 1.69/1.86         ((k4_xboole_0 @ X14 @ X15)
% 1.69/1.86           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.69/1.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.69/1.86  thf('11', plain,
% 1.69/1.86      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 1.69/1.86         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 1.69/1.86            (k2_tarski @ sk_A @ sk_C_1)))),
% 1.69/1.86      inference('sup+', [status(thm)], ['9', '10'])).
% 1.69/1.86  thf(d3_tarski, axiom,
% 1.69/1.86    (![A:$i,B:$i]:
% 1.69/1.86     ( ( r1_tarski @ A @ B ) <=>
% 1.69/1.86       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.69/1.86  thf('12', plain,
% 1.69/1.86      (![X1 : $i, X3 : $i]:
% 1.69/1.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.69/1.86      inference('cnf', [status(esa)], [d3_tarski])).
% 1.69/1.86  thf(d10_xboole_0, axiom,
% 1.69/1.86    (![A:$i,B:$i]:
% 1.69/1.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.69/1.86  thf('13', plain,
% 1.69/1.86      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 1.69/1.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.69/1.86  thf('14', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 1.69/1.86      inference('simplify', [status(thm)], ['13'])).
% 1.69/1.86  thf('15', plain,
% 1.69/1.86      (![X16 : $i, X17 : $i]:
% 1.69/1.86         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.69/1.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.69/1.86  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.69/1.86      inference('sup-', [status(thm)], ['14', '15'])).
% 1.69/1.86  thf('17', plain,
% 1.69/1.86      (![X14 : $i, X15 : $i]:
% 1.69/1.86         ((k4_xboole_0 @ X14 @ X15)
% 1.69/1.86           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.69/1.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.69/1.86  thf('18', plain,
% 1.69/1.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.69/1.86      inference('sup+', [status(thm)], ['16', '17'])).
% 1.69/1.86  thf(d5_xboole_0, axiom,
% 1.69/1.86    (![A:$i,B:$i,C:$i]:
% 1.69/1.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.69/1.86       ( ![D:$i]:
% 1.69/1.86         ( ( r2_hidden @ D @ C ) <=>
% 1.69/1.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.69/1.86  thf('19', plain,
% 1.69/1.86      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.69/1.86         (~ (r2_hidden @ X8 @ X7)
% 1.69/1.86          | (r2_hidden @ X8 @ X5)
% 1.69/1.86          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.69/1.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.69/1.86  thf('20', plain,
% 1.69/1.86      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.69/1.86         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.69/1.86      inference('simplify', [status(thm)], ['19'])).
% 1.69/1.86  thf('21', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]:
% 1.69/1.86         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.69/1.86      inference('sup-', [status(thm)], ['18', '20'])).
% 1.69/1.86  thf('22', plain,
% 1.69/1.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.69/1.86      inference('sup+', [status(thm)], ['16', '17'])).
% 1.69/1.86  thf('23', plain,
% 1.69/1.86      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.69/1.86         (~ (r2_hidden @ X8 @ X7)
% 1.69/1.86          | ~ (r2_hidden @ X8 @ X6)
% 1.69/1.86          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.69/1.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.69/1.86  thf('24', plain,
% 1.69/1.86      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.69/1.86         (~ (r2_hidden @ X8 @ X6)
% 1.69/1.86          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.69/1.86      inference('simplify', [status(thm)], ['23'])).
% 1.69/1.86  thf('25', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]:
% 1.69/1.86         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.69/1.86          | ~ (r2_hidden @ X1 @ X0))),
% 1.69/1.86      inference('sup-', [status(thm)], ['22', '24'])).
% 1.69/1.86  thf('26', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.69/1.86      inference('clc', [status(thm)], ['21', '25'])).
% 1.69/1.86  thf('27', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.69/1.86      inference('sup-', [status(thm)], ['12', '26'])).
% 1.69/1.86  thf('28', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.69/1.86      inference('sup-', [status(thm)], ['12', '26'])).
% 1.69/1.86  thf('29', plain,
% 1.69/1.86      (![X11 : $i, X13 : $i]:
% 1.69/1.86         (((X11) = (X13))
% 1.69/1.86          | ~ (r1_tarski @ X13 @ X11)
% 1.69/1.86          | ~ (r1_tarski @ X11 @ X13))),
% 1.69/1.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.69/1.86  thf('30', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]:
% 1.69/1.86         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 1.69/1.86          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 1.69/1.86      inference('sup-', [status(thm)], ['28', '29'])).
% 1.69/1.86  thf('31', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 1.69/1.86      inference('sup-', [status(thm)], ['27', '30'])).
% 1.69/1.86  thf('32', plain,
% 1.69/1.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.69/1.86      inference('sup+', [status(thm)], ['16', '17'])).
% 1.69/1.86  thf('33', plain,
% 1.69/1.86      (![X18 : $i, X19 : $i]:
% 1.69/1.86         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 1.69/1.86           = (k2_xboole_0 @ X18 @ X19))),
% 1.69/1.86      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.69/1.86  thf('34', plain,
% 1.69/1.86      (![X0 : $i]:
% 1.69/1.86         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 1.69/1.86           = (k2_xboole_0 @ X0 @ X0))),
% 1.69/1.86      inference('sup+', [status(thm)], ['32', '33'])).
% 1.69/1.86  thf(idempotence_k2_xboole_0, axiom,
% 1.69/1.86    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.69/1.86  thf('35', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 1.69/1.86      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.69/1.86  thf('36', plain,
% 1.69/1.86      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 1.69/1.86      inference('demod', [status(thm)], ['34', '35'])).
% 1.69/1.86  thf('37', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]:
% 1.69/1.86         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 1.69/1.86      inference('sup+', [status(thm)], ['31', '36'])).
% 1.69/1.86  thf('38', plain,
% 1.69/1.86      (![X0 : $i]:
% 1.69/1.86         ((k2_xboole_0 @ X0 @ 
% 1.69/1.86           (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)) = (X0))),
% 1.69/1.86      inference('sup+', [status(thm)], ['11', '37'])).
% 1.69/1.86  thf('39', plain,
% 1.69/1.86      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) = (sk_B))),
% 1.69/1.86      inference('sup+', [status(thm)], ['0', '38'])).
% 1.69/1.86  thf('40', plain,
% 1.69/1.86      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) != (sk_B))),
% 1.69/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.86  thf('41', plain,
% 1.69/1.86      (![X27 : $i, X28 : $i]:
% 1.69/1.86         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 1.69/1.86      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.69/1.86  thf(l51_zfmisc_1, axiom,
% 1.69/1.86    (![A:$i,B:$i]:
% 1.69/1.86     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.69/1.86  thf('42', plain,
% 1.69/1.86      (![X38 : $i, X39 : $i]:
% 1.69/1.86         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 1.69/1.86      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.69/1.86  thf('43', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]:
% 1.69/1.86         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.69/1.86      inference('sup+', [status(thm)], ['41', '42'])).
% 1.69/1.86  thf('44', plain,
% 1.69/1.86      (![X38 : $i, X39 : $i]:
% 1.69/1.86         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 1.69/1.86      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.69/1.86  thf('45', plain,
% 1.69/1.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.69/1.86      inference('sup+', [status(thm)], ['43', '44'])).
% 1.69/1.86  thf('46', plain,
% 1.69/1.86      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) != (sk_B))),
% 1.69/1.86      inference('demod', [status(thm)], ['40', '45'])).
% 1.69/1.86  thf('47', plain, ($false),
% 1.69/1.86      inference('simplify_reflect-', [status(thm)], ['39', '46'])).
% 1.69/1.86  
% 1.69/1.86  % SZS output end Refutation
% 1.69/1.86  
% 1.69/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
