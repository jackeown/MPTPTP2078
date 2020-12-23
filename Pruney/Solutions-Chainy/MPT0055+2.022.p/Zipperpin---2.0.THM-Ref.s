%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e87hwStw6y

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:15 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   75 (  84 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 ( 591 expanded)
%              Number of equality atoms :   44 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
 != ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X16: $i] :
      ( ( X16 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ o_0_0_xboole_0 )
      = X25 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('37',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ o_0_0_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ o_0_0_xboole_0 )
      = X22 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','44'])).

thf('46',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B_1 )
 != ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e87hwStw6y
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:05:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 503 iterations in 0.162s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.62  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.44/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(t48_xboole_1, conjecture,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i]:
% 0.44/0.62        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.44/0.62          ( k3_xboole_0 @ A @ B ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.44/0.62         != (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t47_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X28 : $i, X29 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29))
% 0.44/0.62           = (k4_xboole_0 @ X28 @ X29))),
% 0.44/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.44/0.62  thf(t39_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X23 : $i, X24 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.44/0.62           = (k2_xboole_0 @ X23 @ X24))),
% 0.44/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.44/0.62  thf(t40_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X26 : $i, X27 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X27)
% 0.44/0.62           = (k4_xboole_0 @ X26 @ X27))),
% 0.44/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.44/0.62           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.44/0.62  thf(t3_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.44/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.62  thf(d5_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.44/0.62       ( ![D:$i]:
% 0.44/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.62           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X6 @ X5)
% 0.44/0.62          | ~ (r2_hidden @ X6 @ X4)
% 0.44/0.62          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X6 @ X4)
% 0.44/0.62          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.44/0.62          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '8'])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.44/0.62          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '9'])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X10 @ X8)
% 0.44/0.62          | ~ (r2_hidden @ X10 @ X11)
% 0.44/0.62          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ X1 @ X0)
% 0.44/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.44/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.62          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.44/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['12', '15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['11', '17'])).
% 0.44/0.62  thf(t7_xboole_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X16 : $i]:
% 0.44/0.62         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.62  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.44/0.62  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X16 : $i]:
% 0.44/0.62         (((X16) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.44/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf(t4_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.44/0.62          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.44/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((k3_xboole_0 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.44/0.62          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['18', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X28 : $i, X29 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29))
% 0.44/0.62           = (k4_xboole_0 @ X28 @ X29))),
% 0.44/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X0 @ o_0_0_xboole_0)
% 0.44/0.62           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.44/0.62  thf(t3_boole, axiom,
% 0.44/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.62  thf('27', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.62  thf('28', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X25 : $i]: ((k4_xboole_0 @ X25 @ o_0_0_xboole_0) = (X25))),
% 0.44/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('demod', [status(thm)], ['26', '29'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.44/0.62           = (X1))),
% 0.44/0.62      inference('demod', [status(thm)], ['4', '30'])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.44/0.62           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['1', '31'])).
% 0.44/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.62  thf(t17_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i]: (r1_tarski @ (k3_xboole_0 @ X20 @ X21) @ X20)),
% 0.44/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.44/0.62  thf(l32_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X17 : $i, X19 : $i]:
% 0.44/0.62         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 0.44/0.62          | ~ (r1_tarski @ X17 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.62  thf('36', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (![X17 : $i, X19 : $i]:
% 0.44/0.62         (((k4_xboole_0 @ X17 @ X19) = (o_0_0_xboole_0))
% 0.44/0.62          | ~ (r1_tarski @ X17 @ X19))),
% 0.44/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (o_0_0_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (![X23 : $i, X24 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.44/0.62           = (k2_xboole_0 @ X23 @ X24))),
% 0.44/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X1 @ o_0_0_xboole_0)
% 0.44/0.62           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.44/0.62  thf(t1_boole, axiom,
% 0.44/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.62  thf('41', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.44/0.62  thf('42', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X22 : $i]: ((k2_xboole_0 @ X22 @ o_0_0_xboole_0) = (X22))),
% 0.44/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('demod', [status(thm)], ['40', '43'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.44/0.62           = (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['32', '33', '44'])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (((k3_xboole_0 @ sk_A @ sk_B_1) != (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.44/0.62      inference('demod', [status(thm)], ['0', '45'])).
% 0.44/0.62  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
