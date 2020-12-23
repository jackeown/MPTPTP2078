%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9amlueqHYP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:18 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 137 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  481 (1046 expanded)
%              Number of equality atoms :   37 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ ( k1_tarski @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('27',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('44',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','24','43'])).

thf('45',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['26','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9amlueqHYP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 551 iterations in 0.154s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.60  thf(t67_zfmisc_1, conjecture,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.60       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i]:
% 0.43/0.60        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.60          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.43/0.60  thf('0', plain,
% 0.43/0.60      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.43/0.60        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('1', plain,
% 0.43/0.60      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.43/0.60       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.60  thf('3', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.43/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.60  thf(t17_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.43/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.60  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf(l1_zfmisc_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.43/0.60  thf('6', plain,
% 0.43/0.60      (![X45 : $i, X46 : $i]:
% 0.43/0.60         ((r2_hidden @ X45 @ X46) | ~ (r1_tarski @ (k1_tarski @ X45) @ X46))),
% 0.43/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.60  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.43/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf(t79_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.43/0.60  thf('9', plain,
% 0.43/0.60      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.43/0.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.43/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.43/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.43/0.60  thf('11', plain,
% 0.43/0.60      (((r2_hidden @ sk_A @ sk_B_1)
% 0.43/0.60        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('12', plain,
% 0.43/0.60      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('split', [status(esa)], ['11'])).
% 0.43/0.60  thf('13', plain,
% 0.43/0.60      (![X45 : $i, X47 : $i]:
% 0.43/0.60         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 0.43/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.60  thf('14', plain,
% 0.43/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.43/0.60         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.60  thf(t28_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.60  thf('15', plain,
% 0.43/0.60      (![X12 : $i, X13 : $i]:
% 0.43/0.60         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.43/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.60  thf('16', plain,
% 0.43/0.60      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.43/0.60         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.60  thf('17', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.43/0.60         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.43/0.60  thf('19', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.60  thf(t4_xboole_0, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.43/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.43/0.60          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.43/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.60  thf('21', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.60  thf('22', plain,
% 0.43/0.60      ((![X0 : $i]:
% 0.43/0.60          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.60           | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.43/0.60         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['18', '21'])).
% 0.43/0.60  thf('23', plain,
% 0.43/0.60      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.43/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.43/0.60             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['10', '22'])).
% 0.43/0.60  thf('24', plain,
% 0.43/0.60      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.43/0.60       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['7', '23'])).
% 0.43/0.60  thf('25', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.43/0.60      inference('sat_resolution*', [status(thm)], ['2', '24'])).
% 0.43/0.60  thf('26', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.43/0.60      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.43/0.60  thf(l27_zfmisc_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.43/0.60  thf('27', plain,
% 0.43/0.60      (![X48 : $i, X49 : $i]:
% 0.43/0.60         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.43/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.43/0.60  thf('28', plain,
% 0.43/0.60      (![X3 : $i, X4 : $i]:
% 0.43/0.60         ((r1_xboole_0 @ X3 @ X4)
% 0.43/0.60          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.60  thf('29', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.60  thf('30', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.60  thf('31', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.43/0.60  thf(t7_xboole_0, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.60  thf('32', plain,
% 0.43/0.60      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.60  thf('33', plain,
% 0.43/0.60      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.43/0.60          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.43/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.60  thf('34', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.60  thf('35', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((r2_hidden @ X0 @ X1)
% 0.43/0.60          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['31', '34'])).
% 0.43/0.60  thf('36', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.60  thf(t100_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.60  thf('37', plain,
% 0.43/0.60      (![X8 : $i, X9 : $i]:
% 0.43/0.60         ((k4_xboole_0 @ X8 @ X9)
% 0.43/0.60           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.60  thf('38', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.43/0.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.60      inference('sup+', [status(thm)], ['36', '37'])).
% 0.43/0.60  thf('39', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.43/0.60            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.43/0.60          | (r2_hidden @ X0 @ X1))),
% 0.43/0.60      inference('sup+', [status(thm)], ['35', '38'])).
% 0.43/0.60  thf(t5_boole, axiom,
% 0.43/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.60  thf('40', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.43/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.60  thf('41', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.43/0.60          | (r2_hidden @ X0 @ X1))),
% 0.43/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.43/0.60  thf('42', plain,
% 0.43/0.60      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.43/0.60         <= (~
% 0.43/0.60             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.43/0.60      inference('split', [status(esa)], ['11'])).
% 0.43/0.60  thf('43', plain,
% 0.43/0.60      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.43/0.60       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.43/0.60      inference('split', [status(esa)], ['11'])).
% 0.43/0.60  thf('44', plain,
% 0.43/0.60      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.43/0.60      inference('sat_resolution*', [status(thm)], ['2', '24', '43'])).
% 0.43/0.60  thf('45', plain,
% 0.43/0.60      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.43/0.60      inference('simpl_trail', [status(thm)], ['42', '44'])).
% 0.43/0.60  thf('46', plain,
% 0.43/0.60      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.43/0.60        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['41', '45'])).
% 0.43/0.60  thf('47', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.43/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.43/0.60  thf('48', plain, ($false), inference('demod', [status(thm)], ['26', '47'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
