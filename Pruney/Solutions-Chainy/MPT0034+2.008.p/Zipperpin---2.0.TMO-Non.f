%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y2ofLgIql6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:55 EST 2020

% Result     : Timeout 59.30s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   68 ( 212 expanded)
%              Number of leaves         :   20 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  506 (1531 expanded)
%              Number of equality atoms :   18 (  68 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X2 ) @ X1 ) @ X3 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X2 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ ( sk_D @ X15 @ X14 @ X13 ) @ X15 )
      | ( X13
        = ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r1_tarski @ ( sk_D @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_D @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ~ ( r1_tarski @ ( sk_D @ X15 @ X14 @ X13 ) @ X13 )
      | ( X13
        = ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t26_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t26_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X3 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) @ X2 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X3 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y2ofLgIql6
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 59.30/59.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 59.30/59.57  % Solved by: fo/fo7.sh
% 59.30/59.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.30/59.57  % done 36748 iterations in 59.137s
% 59.30/59.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 59.30/59.57  % SZS output start Refutation
% 59.30/59.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 59.30/59.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 59.30/59.57  thf(sk_C_type, type, sk_C: $i).
% 59.30/59.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 59.30/59.57  thf(sk_B_type, type, sk_B: $i).
% 59.30/59.57  thf(sk_A_type, type, sk_A: $i).
% 59.30/59.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.30/59.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 59.30/59.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 59.30/59.57  thf(t27_xboole_1, conjecture,
% 59.30/59.57    (![A:$i,B:$i,C:$i,D:$i]:
% 59.30/59.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 59.30/59.57       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 59.30/59.57  thf(zf_stmt_0, negated_conjecture,
% 59.30/59.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 59.30/59.57        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 59.30/59.57          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 59.30/59.57    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 59.30/59.57  thf('0', plain,
% 59.30/59.57      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 59.30/59.57          (k3_xboole_0 @ sk_B @ sk_D_1))),
% 59.30/59.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.30/59.57  thf('1', plain, ((r1_tarski @ sk_C @ sk_D_1)),
% 59.30/59.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.30/59.57  thf(t17_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 59.30/59.57  thf('2', plain,
% 59.30/59.57      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 59.30/59.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 59.30/59.57  thf(t12_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i]:
% 59.30/59.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 59.30/59.57  thf('3', plain,
% 59.30/59.57      (![X3 : $i, X4 : $i]:
% 59.30/59.57         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 59.30/59.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 59.30/59.57  thf('4', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 59.30/59.57      inference('sup-', [status(thm)], ['2', '3'])).
% 59.30/59.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 59.30/59.57  thf('5', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 59.30/59.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 59.30/59.57  thf('6', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 59.30/59.57      inference('sup-', [status(thm)], ['2', '3'])).
% 59.30/59.57  thf(t11_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i,C:$i]:
% 59.30/59.57     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 59.30/59.57  thf('7', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 59.30/59.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 59.30/59.57  thf('8', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 59.30/59.57      inference('sup-', [status(thm)], ['6', '7'])).
% 59.30/59.57  thf('9', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ X0)),
% 59.30/59.57      inference('sup-', [status(thm)], ['5', '8'])).
% 59.30/59.57  thf('10', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 59.30/59.57      inference('sup-', [status(thm)], ['6', '7'])).
% 59.30/59.57  thf('11', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ X2) @ 
% 59.30/59.57          X0)),
% 59.30/59.57      inference('sup-', [status(thm)], ['9', '10'])).
% 59.30/59.57  thf(t9_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i,C:$i]:
% 59.30/59.57     ( ( r1_tarski @ A @ B ) =>
% 59.30/59.57       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 59.30/59.57  thf('12', plain,
% 59.30/59.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X22 @ X23)
% 59.30/59.57          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ (k2_xboole_0 @ X23 @ X24)))),
% 59.30/59.57      inference('cnf', [status(esa)], [t9_xboole_1])).
% 59.30/59.57  thf('13', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.30/59.57         (r1_tarski @ 
% 59.30/59.57          (k2_xboole_0 @ 
% 59.30/59.57           (k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X2) @ X1) @ X3) @ 
% 59.30/59.57          (k2_xboole_0 @ X0 @ X3))),
% 59.30/59.57      inference('sup-', [status(thm)], ['11', '12'])).
% 59.30/59.57  thf('14', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ X2) @ 
% 59.30/59.57          X0)),
% 59.30/59.57      inference('sup-', [status(thm)], ['9', '10'])).
% 59.30/59.57  thf('15', plain,
% 59.30/59.57      (![X3 : $i, X4 : $i]:
% 59.30/59.57         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 59.30/59.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 59.30/59.57  thf('16', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         ((k2_xboole_0 @ 
% 59.30/59.57           (k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X2) @ X1) @ X0) = (
% 59.30/59.57           X0))),
% 59.30/59.57      inference('sup-', [status(thm)], ['14', '15'])).
% 59.30/59.57  thf('17', plain,
% 59.30/59.57      (![X0 : $i, X3 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X0 @ X3))),
% 59.30/59.57      inference('demod', [status(thm)], ['13', '16'])).
% 59.30/59.57  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 59.30/59.57      inference('sup+', [status(thm)], ['4', '17'])).
% 59.30/59.57  thf(t7_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 59.30/59.57  thf('19', plain,
% 59.30/59.57      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 59.30/59.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 59.30/59.57  thf(t20_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i,C:$i]:
% 59.30/59.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 59.30/59.57         ( ![D:$i]:
% 59.30/59.57           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 59.30/59.57             ( r1_tarski @ D @ A ) ) ) ) =>
% 59.30/59.57       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 59.30/59.57  thf('20', plain,
% 59.30/59.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X13 @ X14)
% 59.30/59.57          | ~ (r1_tarski @ X13 @ X15)
% 59.30/59.57          | (r1_tarski @ (sk_D @ X15 @ X14 @ X13) @ X15)
% 59.30/59.57          | ((X13) = (k3_xboole_0 @ X14 @ X15)))),
% 59.30/59.57      inference('cnf', [status(esa)], [t20_xboole_1])).
% 59.30/59.57  thf('21', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (((X1) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 59.30/59.57          | (r1_tarski @ (sk_D @ X2 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 59.30/59.57          | ~ (r1_tarski @ X1 @ X2))),
% 59.30/59.57      inference('sup-', [status(thm)], ['19', '20'])).
% 59.30/59.57  thf('22', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         ((r1_tarski @ (sk_D @ X0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ X0)
% 59.30/59.57          | ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 59.30/59.57      inference('sup-', [status(thm)], ['18', '21'])).
% 59.30/59.57  thf('23', plain,
% 59.30/59.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X13 @ X14)
% 59.30/59.57          | ~ (r1_tarski @ X13 @ X15)
% 59.30/59.57          | ~ (r1_tarski @ (sk_D @ X15 @ X14 @ X13) @ X13)
% 59.30/59.57          | ((X13) = (k3_xboole_0 @ X14 @ X15)))),
% 59.30/59.57      inference('cnf', [status(esa)], [t20_xboole_1])).
% 59.30/59.57  thf('24', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         (((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 59.30/59.57          | ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 59.30/59.57          | ~ (r1_tarski @ X0 @ X0)
% 59.30/59.57          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 59.30/59.57      inference('sup-', [status(thm)], ['22', '23'])).
% 59.30/59.57  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 59.30/59.57      inference('sup+', [status(thm)], ['4', '17'])).
% 59.30/59.57  thf('26', plain,
% 59.30/59.57      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 59.30/59.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 59.30/59.57  thf('27', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         (((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 59.30/59.57          | ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 59.30/59.57      inference('demod', [status(thm)], ['24', '25', '26'])).
% 59.30/59.57  thf('28', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 59.30/59.57      inference('simplify', [status(thm)], ['27'])).
% 59.30/59.57  thf('29', plain,
% 59.30/59.57      (![X0 : $i, X3 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X0 @ X3))),
% 59.30/59.57      inference('demod', [status(thm)], ['13', '16'])).
% 59.30/59.57  thf('30', plain,
% 59.30/59.57      (![X3 : $i, X4 : $i]:
% 59.30/59.57         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 59.30/59.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 59.30/59.57  thf('31', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 59.30/59.57           = (k2_xboole_0 @ X1 @ X0))),
% 59.30/59.57      inference('sup-', [status(thm)], ['29', '30'])).
% 59.30/59.57  thf('32', plain,
% 59.30/59.57      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 59.30/59.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 59.30/59.57  thf(t26_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i,C:$i]:
% 59.30/59.57     ( ( r1_tarski @ A @ B ) =>
% 59.30/59.57       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ))).
% 59.30/59.57  thf('33', plain,
% 59.30/59.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X16 @ X17)
% 59.30/59.57          | (r1_tarski @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X18)))),
% 59.30/59.57      inference('cnf', [status(esa)], [t26_xboole_1])).
% 59.30/59.57  thf('34', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ 
% 59.30/59.57          (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 59.30/59.57      inference('sup-', [status(thm)], ['32', '33'])).
% 59.30/59.57  thf(t1_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i,C:$i]:
% 59.30/59.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 59.30/59.57       ( r1_tarski @ A @ C ) ))).
% 59.30/59.57  thf('35', plain,
% 59.30/59.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X10 @ X11)
% 59.30/59.57          | ~ (r1_tarski @ X11 @ X12)
% 59.30/59.57          | (r1_tarski @ X10 @ X12))),
% 59.30/59.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 59.30/59.57  thf('36', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.30/59.57         ((r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X3)
% 59.30/59.57          | ~ (r1_tarski @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3))),
% 59.30/59.57      inference('sup-', [status(thm)], ['34', '35'])).
% 59.30/59.57  thf('37', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.30/59.57         (~ (r1_tarski @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3) @ X2)
% 59.30/59.57          | (r1_tarski @ (k3_xboole_0 @ X0 @ X3) @ X2))),
% 59.30/59.57      inference('sup-', [status(thm)], ['31', '36'])).
% 59.30/59.57  thf('38', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 59.30/59.57      inference('sup-', [status(thm)], ['28', '37'])).
% 59.30/59.57  thf('39', plain,
% 59.30/59.57      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_D_1)),
% 59.30/59.57      inference('sup-', [status(thm)], ['1', '38'])).
% 59.30/59.57  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 59.30/59.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.30/59.57  thf('41', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 59.30/59.57      inference('sup-', [status(thm)], ['6', '7'])).
% 59.30/59.57  thf('42', plain,
% 59.30/59.57      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 59.30/59.57      inference('sup-', [status(thm)], ['40', '41'])).
% 59.30/59.57  thf(t19_xboole_1, axiom,
% 59.30/59.57    (![A:$i,B:$i,C:$i]:
% 59.30/59.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 59.30/59.57       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 59.30/59.57  thf('43', plain,
% 59.30/59.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 59.30/59.57         (~ (r1_tarski @ X7 @ X8)
% 59.30/59.57          | ~ (r1_tarski @ X7 @ X9)
% 59.30/59.57          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 59.30/59.57      inference('cnf', [status(esa)], [t19_xboole_1])).
% 59.30/59.57  thf('44', plain,
% 59.30/59.57      (![X0 : $i, X1 : $i]:
% 59.30/59.57         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))
% 59.30/59.57          | ~ (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X1))),
% 59.30/59.57      inference('sup-', [status(thm)], ['42', '43'])).
% 59.30/59.57  thf('45', plain,
% 59.30/59.57      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D_1))),
% 59.30/59.57      inference('sup-', [status(thm)], ['39', '44'])).
% 59.30/59.57  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 59.30/59.57  
% 59.30/59.57  % SZS output end Refutation
% 59.30/59.57  
% 59.30/59.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
