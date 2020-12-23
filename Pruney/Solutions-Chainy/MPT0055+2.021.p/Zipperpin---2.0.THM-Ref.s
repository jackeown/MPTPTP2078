%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dn3TRoyyYG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:15 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   71 (  80 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  464 ( 563 expanded)
%              Number of equality atoms :   43 (  48 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ o_0_0_xboole_0 )
      = X23 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','29'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ o_0_0_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ o_0_0_xboole_0 )
      = X20 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','42'])).

thf('44',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dn3TRoyyYG
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.48/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.64  % Solved by: fo/fo7.sh
% 0.48/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.64  % done 465 iterations in 0.200s
% 0.48/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.64  % SZS output start Refutation
% 0.48/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.64  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.48/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.64  thf(t48_xboole_1, conjecture,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.64    (~( ![A:$i,B:$i]:
% 0.48/0.64        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.48/0.64          ( k3_xboole_0 @ A @ B ) ) )),
% 0.48/0.64    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.48/0.64  thf('0', plain,
% 0.48/0.64      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.48/0.64         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.64  thf(t47_xboole_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.48/0.64  thf('1', plain,
% 0.48/0.64      (![X26 : $i, X27 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27))
% 0.48/0.64           = (k4_xboole_0 @ X26 @ X27))),
% 0.48/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.48/0.64  thf(t39_xboole_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.64  thf('2', plain,
% 0.48/0.64      (![X21 : $i, X22 : $i]:
% 0.48/0.64         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.48/0.64           = (k2_xboole_0 @ X21 @ X22))),
% 0.48/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.64  thf(t40_xboole_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.48/0.64  thf('3', plain,
% 0.48/0.64      (![X24 : $i, X25 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X25)
% 0.48/0.64           = (k4_xboole_0 @ X24 @ X25))),
% 0.48/0.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.64  thf('4', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.64           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.48/0.64      inference('sup+', [status(thm)], ['2', '3'])).
% 0.48/0.64  thf(t3_xboole_0, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.48/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.64            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.48/0.64  thf('5', plain,
% 0.48/0.64      (![X11 : $i, X12 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.48/0.64  thf('6', plain,
% 0.48/0.64      (![X11 : $i, X12 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.48/0.64  thf(d5_xboole_0, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i]:
% 0.48/0.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.48/0.64       ( ![D:$i]:
% 0.48/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.48/0.64  thf('7', plain,
% 0.48/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.48/0.64         (~ (r2_hidden @ X6 @ X5)
% 0.48/0.64          | ~ (r2_hidden @ X6 @ X4)
% 0.48/0.64          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.48/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.48/0.64  thf('8', plain,
% 0.48/0.64      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.48/0.64         (~ (r2_hidden @ X6 @ X4)
% 0.48/0.64          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.48/0.64      inference('simplify', [status(thm)], ['7'])).
% 0.48/0.64  thf('9', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.48/0.64          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['6', '8'])).
% 0.48/0.64  thf('10', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.48/0.64          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['5', '9'])).
% 0.48/0.64  thf('11', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.48/0.64      inference('simplify', [status(thm)], ['10'])).
% 0.48/0.64  thf('12', plain,
% 0.48/0.64      (![X11 : $i, X12 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.48/0.64  thf('13', plain,
% 0.48/0.64      (![X11 : $i, X12 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.48/0.64  thf('14', plain,
% 0.48/0.64      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.48/0.64         (~ (r2_hidden @ X13 @ X11)
% 0.48/0.64          | ~ (r2_hidden @ X13 @ X14)
% 0.48/0.64          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.48/0.64  thf('15', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ X1 @ X0)
% 0.48/0.64          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.48/0.64          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.48/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.64  thf('16', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((r1_xboole_0 @ X0 @ X1)
% 0.48/0.64          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.48/0.64          | (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.64      inference('sup-', [status(thm)], ['12', '15'])).
% 0.48/0.64  thf('17', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.48/0.64  thf('18', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['11', '17'])).
% 0.48/0.64  thf(d7_xboole_0, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.48/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.64  thf('19', plain,
% 0.48/0.64      (![X8 : $i, X9 : $i]:
% 0.48/0.64         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.48/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.64  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.48/0.64  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.48/0.64      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.48/0.64  thf('21', plain,
% 0.48/0.64      (![X8 : $i, X9 : $i]:
% 0.48/0.64         (((k3_xboole_0 @ X8 @ X9) = (o_0_0_xboole_0))
% 0.48/0.64          | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.48/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.48/0.64  thf('22', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['18', '21'])).
% 0.48/0.64  thf('23', plain,
% 0.48/0.64      (![X26 : $i, X27 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27))
% 0.48/0.64           = (k4_xboole_0 @ X26 @ X27))),
% 0.48/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.48/0.64  thf('24', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ X0 @ o_0_0_xboole_0)
% 0.48/0.64           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.64      inference('sup+', [status(thm)], ['22', '23'])).
% 0.48/0.64  thf(t3_boole, axiom,
% 0.48/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.64  thf('25', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.64  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.48/0.64      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.48/0.64  thf('27', plain,
% 0.48/0.64      (![X23 : $i]: ((k4_xboole_0 @ X23 @ o_0_0_xboole_0) = (X23))),
% 0.48/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.48/0.64  thf('28', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.64      inference('demod', [status(thm)], ['24', '27'])).
% 0.48/0.64  thf('29', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.64           = (X1))),
% 0.48/0.64      inference('demod', [status(thm)], ['4', '28'])).
% 0.48/0.64  thf('30', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.48/0.64           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.64      inference('sup+', [status(thm)], ['1', '29'])).
% 0.48/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.64  thf('31', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.64  thf(t17_xboole_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.64  thf('32', plain,
% 0.48/0.64      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 0.48/0.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.48/0.64  thf(l32_xboole_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.64  thf('33', plain,
% 0.48/0.64      (![X15 : $i, X17 : $i]:
% 0.48/0.64         (((k4_xboole_0 @ X15 @ X17) = (k1_xboole_0))
% 0.48/0.64          | ~ (r1_tarski @ X15 @ X17))),
% 0.48/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.48/0.64  thf('34', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.48/0.64      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.48/0.64  thf('35', plain,
% 0.48/0.64      (![X15 : $i, X17 : $i]:
% 0.48/0.64         (((k4_xboole_0 @ X15 @ X17) = (o_0_0_xboole_0))
% 0.48/0.64          | ~ (r1_tarski @ X15 @ X17))),
% 0.48/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.48/0.64  thf('36', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (o_0_0_xboole_0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['32', '35'])).
% 0.48/0.64  thf('37', plain,
% 0.48/0.64      (![X21 : $i, X22 : $i]:
% 0.48/0.64         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.48/0.64           = (k2_xboole_0 @ X21 @ X22))),
% 0.48/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.64  thf('38', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k2_xboole_0 @ X1 @ o_0_0_xboole_0)
% 0.48/0.64           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.64      inference('sup+', [status(thm)], ['36', '37'])).
% 0.48/0.64  thf(t1_boole, axiom,
% 0.48/0.64    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.64  thf('39', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.48/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.64  thf('40', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.48/0.64      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.48/0.64  thf('41', plain,
% 0.48/0.64      (![X20 : $i]: ((k2_xboole_0 @ X20 @ o_0_0_xboole_0) = (X20))),
% 0.48/0.64      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.64  thf('42', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.64      inference('demod', [status(thm)], ['38', '41'])).
% 0.48/0.64  thf('43', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.48/0.64           = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.64      inference('demod', [status(thm)], ['30', '31', '42'])).
% 0.48/0.64  thf('44', plain,
% 0.48/0.64      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.64      inference('demod', [status(thm)], ['0', '43'])).
% 0.48/0.64  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.48/0.64  
% 0.48/0.64  % SZS output end Refutation
% 0.48/0.64  
% 0.48/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
