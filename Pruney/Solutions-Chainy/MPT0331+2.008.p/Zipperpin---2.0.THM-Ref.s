%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8N8ZdMoBc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:04 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   70 (  94 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  450 ( 649 expanded)
%              Number of equality atoms :   47 (  67 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X27 )
        = ( k2_tarski @ X24 @ X26 ) )
      | ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','27','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','41'])).

thf('43',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8N8ZdMoBc
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.74/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/1.01  % Solved by: fo/fo7.sh
% 0.74/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/1.01  % done 1437 iterations in 0.565s
% 0.74/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/1.01  % SZS output start Refutation
% 0.74/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.74/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.74/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.74/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.74/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.74/1.01  thf(t144_zfmisc_1, conjecture,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.74/1.01          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.74/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.74/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.74/1.01        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.74/1.01             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.74/1.01    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.74/1.01  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf(t72_zfmisc_1, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.74/1.01       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.74/1.01  thf('1', plain,
% 0.74/1.01      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.74/1.01         (((k4_xboole_0 @ (k2_tarski @ X24 @ X26) @ X27)
% 0.74/1.01            = (k2_tarski @ X24 @ X26))
% 0.74/1.01          | (r2_hidden @ X26 @ X27)
% 0.74/1.01          | (r2_hidden @ X24 @ X27))),
% 0.74/1.01      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.74/1.01  thf(t48_xboole_1, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/1.01  thf('2', plain,
% 0.74/1.01      (![X14 : $i, X15 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.74/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.74/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/1.01  thf(t36_xboole_1, axiom,
% 0.74/1.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.74/1.01  thf('3', plain,
% 0.74/1.01      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.74/1.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/1.01  thf(l32_xboole_1, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/1.01  thf('4', plain,
% 0.74/1.01      (![X5 : $i, X7 : $i]:
% 0.74/1.01         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.74/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.01  thf('5', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/1.01  thf('6', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.74/1.01      inference('sup+', [status(thm)], ['2', '5'])).
% 0.74/1.01  thf(t49_xboole_1, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.74/1.01       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.74/1.01  thf('7', plain,
% 0.74/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.74/1.01         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.74/1.01           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.74/1.01      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.74/1.01  thf('8', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.74/1.01      inference('demod', [status(thm)], ['6', '7'])).
% 0.74/1.01  thf(t100_xboole_1, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.74/1.01  thf('9', plain,
% 0.74/1.01      (![X8 : $i, X9 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X8 @ X9)
% 0.74/1.01           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.74/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/1.01  thf('10', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.74/1.01           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/1.01      inference('sup+', [status(thm)], ['8', '9'])).
% 0.74/1.01  thf(d10_xboole_0, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/1.01  thf('11', plain,
% 0.74/1.01      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.74/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/1.01  thf('12', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.74/1.01      inference('simplify', [status(thm)], ['11'])).
% 0.74/1.01  thf('13', plain,
% 0.74/1.01      (![X5 : $i, X7 : $i]:
% 0.74/1.01         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.74/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.01  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/1.01  thf('15', plain,
% 0.74/1.01      (![X14 : $i, X15 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.74/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.74/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/1.01  thf('16', plain,
% 0.74/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.74/1.01      inference('sup+', [status(thm)], ['14', '15'])).
% 0.74/1.01  thf('17', plain,
% 0.74/1.01      (![X14 : $i, X15 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.74/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.74/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/1.01  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/1.01  thf('19', plain,
% 0.74/1.01      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.74/1.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/1.01  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.74/1.01      inference('sup+', [status(thm)], ['18', '19'])).
% 0.74/1.01  thf('21', plain,
% 0.74/1.01      (![X5 : $i, X7 : $i]:
% 0.74/1.01         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.74/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.01  thf('22', plain,
% 0.74/1.01      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['20', '21'])).
% 0.74/1.01  thf('23', plain,
% 0.74/1.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/1.01      inference('sup+', [status(thm)], ['17', '22'])).
% 0.74/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.74/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.74/1.01  thf('24', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/1.01  thf('25', plain,
% 0.74/1.01      (![X8 : $i, X9 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X8 @ X9)
% 0.74/1.01           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.74/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/1.01  thf('26', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X0 @ X1)
% 0.74/1.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['24', '25'])).
% 0.74/1.01  thf('27', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/1.01      inference('sup+', [status(thm)], ['23', '26'])).
% 0.74/1.01  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/1.01  thf(t47_xboole_1, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.74/1.01  thf('29', plain,
% 0.74/1.01      (![X12 : $i, X13 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.74/1.01           = (k4_xboole_0 @ X12 @ X13))),
% 0.74/1.01      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/1.01  thf('30', plain,
% 0.74/1.01      (![X5 : $i, X6 : $i]:
% 0.74/1.01         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.74/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.01  thf('31', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.74/1.01          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/1.01  thf('32', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((k1_xboole_0) != (k1_xboole_0))
% 0.74/1.01          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['28', '31'])).
% 0.74/1.01  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['32'])).
% 0.74/1.01  thf('34', plain,
% 0.74/1.01      (![X2 : $i, X4 : $i]:
% 0.74/1.01         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.74/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/1.01  thf('35', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ X0) @ X0)
% 0.74/1.01          | ((k3_xboole_0 @ X0 @ X0) = (X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['33', '34'])).
% 0.74/1.01  thf('36', plain,
% 0.74/1.01      (![X14 : $i, X15 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.74/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.74/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/1.01  thf('37', plain,
% 0.74/1.01      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.74/1.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/1.01  thf('38', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.74/1.01      inference('sup+', [status(thm)], ['36', '37'])).
% 0.74/1.01  thf('39', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/1.01      inference('demod', [status(thm)], ['35', '38'])).
% 0.74/1.01  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/1.01      inference('demod', [status(thm)], ['16', '27', '39'])).
% 0.74/1.01  thf('41', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i]:
% 0.74/1.01         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.74/1.01      inference('demod', [status(thm)], ['10', '40'])).
% 0.74/1.01  thf('42', plain,
% 0.74/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.01         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 0.74/1.01          | (r2_hidden @ X1 @ X2)
% 0.74/1.01          | (r2_hidden @ X0 @ X2))),
% 0.74/1.01      inference('sup+', [status(thm)], ['1', '41'])).
% 0.74/1.01  thf('43', plain,
% 0.74/1.01      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('44', plain,
% 0.74/1.01      ((((sk_C) != (sk_C))
% 0.74/1.01        | (r2_hidden @ sk_B @ sk_C)
% 0.74/1.01        | (r2_hidden @ sk_A @ sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['42', '43'])).
% 0.74/1.01  thf('45', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.74/1.01      inference('simplify', [status(thm)], ['44'])).
% 0.74/1.01  thf('46', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('47', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.74/1.01      inference('clc', [status(thm)], ['45', '46'])).
% 0.74/1.01  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.74/1.01  
% 0.74/1.01  % SZS output end Refutation
% 0.74/1.01  
% 0.83/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
