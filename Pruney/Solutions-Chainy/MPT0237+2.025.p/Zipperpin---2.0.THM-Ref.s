%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ElrnNRR7x2

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:02 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 274 expanded)
%              Number of leaves         :   26 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  510 (2008 expanded)
%              Number of equality atoms :   68 ( 256 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X52 ) )
        = ( k2_tarski @ X51 @ X52 ) )
      | ( X51 = X52 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X50 ) )
      | ( X49 = X50 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('49',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','47','48','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ElrnNRR7x2
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:06:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 541 iterations in 0.281s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(t32_zfmisc_1, conjecture,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.54/0.74       ( k2_tarski @ A @ B ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i]:
% 0.54/0.74        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.54/0.74          ( k2_tarski @ A @ B ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.54/0.74         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(l51_zfmisc_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      (![X47 : $i, X48 : $i]:
% 0.54/0.74         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.54/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.54/0.74         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['0', '1'])).
% 0.54/0.74  thf(t29_zfmisc_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) != ( B ) ) =>
% 0.54/0.74       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.54/0.74         ( k2_tarski @ A @ B ) ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X51 : $i, X52 : $i]:
% 0.54/0.74         (((k5_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X52))
% 0.54/0.74            = (k2_tarski @ X51 @ X52))
% 0.54/0.74          | ((X51) = (X52)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.54/0.74  thf(t17_zfmisc_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) != ( B ) ) =>
% 0.54/0.74       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      (![X49 : $i, X50 : $i]:
% 0.54/0.74         ((r1_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X50))
% 0.54/0.74          | ((X49) = (X50)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.54/0.74  thf(t83_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (![X14 : $i, X15 : $i]:
% 0.54/0.74         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.54/0.74      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((X1) = (X0))
% 0.54/0.74          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.54/0.74              = (k1_tarski @ X1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.74  thf(t98_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.54/0.74           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.54/0.74            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.54/0.74          | ((X0) = (X1)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['6', '7'])).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.54/0.74            = (k2_tarski @ X1 @ X0))
% 0.54/0.74          | ((X1) = (X0))
% 0.54/0.74          | ((X0) = (X1)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['3', '8'])).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((X1) = (X0))
% 0.54/0.74          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.54/0.74              = (k2_tarski @ X1 @ X0)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['9'])).
% 0.54/0.74  thf('11', plain,
% 0.54/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.54/0.74         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['0', '1'])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      ((((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))
% 0.54/0.74        | ((sk_A) = (sk_B_1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf('13', plain, (((sk_A) = (sk_B_1))),
% 0.54/0.74      inference('simplify', [status(thm)], ['12'])).
% 0.54/0.74  thf(idempotence_k3_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.54/0.74  thf('14', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.54/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.54/0.74  thf(t100_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.74  thf('15', plain,
% 0.54/0.74      (![X8 : $i, X9 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X8 @ X9)
% 0.54/0.74           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.74  thf('16', plain,
% 0.54/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.74  thf('17', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.54/0.74           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ X0 @ X0)
% 0.54/0.74           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.74  thf(t48_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (![X10 : $i, X11 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.54/0.74           = (k3_xboole_0 @ X10 @ X11))),
% 0.54/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.54/0.74           = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.74  thf('22', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.54/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.54/0.74  thf('23', plain,
% 0.54/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.54/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      (![X10 : $i, X11 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.54/0.74           = (k3_xboole_0 @ X10 @ X11))),
% 0.54/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X0 @ X0)
% 0.54/0.74           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['23', '24'])).
% 0.54/0.74  thf('26', plain,
% 0.54/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.74  thf('27', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k5_xboole_0 @ X0 @ X0)
% 0.54/0.74           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.74  thf('28', plain,
% 0.54/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.54/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.74  thf(t79_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.54/0.74  thf('29', plain,
% 0.54/0.74      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.54/0.74      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.54/0.74  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['28', '29'])).
% 0.54/0.74  thf(t7_xboole_0, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.74          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.54/0.74  thf('31', plain,
% 0.54/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.54/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.54/0.74  thf(t4_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.54/0.74          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['30', '33'])).
% 0.54/0.74  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['27', '34'])).
% 0.54/0.74  thf('36', plain,
% 0.54/0.74      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['18', '35'])).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k5_xboole_0 @ X0 @ X0)
% 0.54/0.74           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.74  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['27', '34'])).
% 0.54/0.74  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['27', '34'])).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      (![X8 : $i, X9 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X8 @ X9)
% 0.54/0.74           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.74  thf('42', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('43', plain,
% 0.54/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.54/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.74  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['27', '34'])).
% 0.54/0.74  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.74  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['42', '45'])).
% 0.54/0.74  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.74      inference('demod', [status(thm)], ['36', '46'])).
% 0.54/0.74  thf('48', plain, (((sk_A) = (sk_B_1))),
% 0.54/0.74      inference('simplify', [status(thm)], ['12'])).
% 0.54/0.74  thf(t69_enumset1, axiom,
% 0.54/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.54/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.74  thf('50', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['2', '13', '47', '48', '49'])).
% 0.54/0.74  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
