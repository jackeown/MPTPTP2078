%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P1Jl1QtyWR

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:34 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   70 (  88 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  470 ( 632 expanded)
%              Number of equality atoms :   43 (  60 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X52 @ X54 ) @ X55 )
      | ~ ( r2_hidden @ X54 @ X55 )
      | ~ ( r2_hidden @ X52 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B_1 )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','32'])).

thf('34',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['10','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P1Jl1QtyWR
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:01:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 391 iterations in 0.143s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(t48_zfmisc_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.42/0.60       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.42/0.60          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.42/0.60  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain, ((r2_hidden @ sk_C @ sk_B_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t38_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.42/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X52 : $i, X54 : $i, X55 : $i]:
% 0.42/0.60         ((r1_tarski @ (k2_tarski @ X52 @ X54) @ X55)
% 0.42/0.60          | ~ (r2_hidden @ X54 @ X55)
% 0.42/0.60          | ~ (r2_hidden @ X52 @ X55))),
% 0.42/0.60      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.42/0.60          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf(t28_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i]:
% 0.42/0.60         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B_1)
% 0.42/0.60         = (k2_tarski @ sk_A @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (((k3_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C))
% 0.42/0.60         = (k2_tarski @ sk_A @ sk_C))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf(t100_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X10 @ X11)
% 0.42/0.60           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (((k4_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C))
% 0.42/0.60         = (k5_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf(commutativity_k5_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.42/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.60  thf('12', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X10 @ X11)
% 0.42/0.60           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.42/0.60  thf(t7_xboole_0, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.42/0.60  thf(t1_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.42/0.60       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         ((r2_hidden @ X5 @ X6)
% 0.42/0.60          | (r2_hidden @ X5 @ X7)
% 0.42/0.60          | ~ (r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.42/0.60          | (r2_hidden @ X1 @ X0)
% 0.42/0.60          | (r2_hidden @ X1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X5 @ X6)
% 0.42/0.60          | ~ (r2_hidden @ X5 @ X7)
% 0.42/0.60          | ~ (r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.42/0.60          | ~ (r2_hidden @ X1 @ X0)
% 0.42/0.60          | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X1 @ X0)
% 0.42/0.60          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('clc', [status(thm)], ['19', '23'])).
% 0.42/0.60  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '24'])).
% 0.42/0.60  thf('26', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '25'])).
% 0.42/0.60  thf(t91_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.42/0.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.42/0.60           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.42/0.60           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.42/0.60  thf(t5_boole, axiom,
% 0.42/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.60  thf('30', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.42/0.60  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['28', '31'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['11', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (((sk_B_1)
% 0.42/0.60         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ 
% 0.42/0.60            (k4_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['10', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf(t94_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k2_xboole_0 @ A @ B ) =
% 0.42/0.60       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X21 : $i, X22 : $i]:
% 0.42/0.60         ((k2_xboole_0 @ X21 @ X22)
% 0.42/0.60           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.42/0.60              (k3_xboole_0 @ X21 @ X22)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.42/0.60           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X21 : $i, X22 : $i]:
% 0.42/0.60         ((k2_xboole_0 @ X21 @ X22)
% 0.42/0.60           = (k5_xboole_0 @ X21 @ 
% 0.42/0.60              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.42/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k2_xboole_0 @ X0 @ X1)
% 0.42/0.60           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['35', '38'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X10 @ X11)
% 0.42/0.60           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k2_xboole_0 @ X0 @ X1)
% 0.42/0.60           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (((sk_B_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['34', '41'])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B_1) != (sk_B_1))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('44', plain, ($false),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
