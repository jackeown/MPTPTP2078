%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jaFDCOJcYf

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  467 ( 792 expanded)
%              Number of equality atoms :   60 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
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
    ! [X65: $i,X66: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X65 ) @ ( k1_tarski @ X66 ) )
        = ( k2_tarski @ X65 @ X66 ) )
      | ( X65 = X66 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X63 ) @ ( k1_tarski @ X64 ) )
      | ( X63 = X64 ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

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
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
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

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('44',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','42','43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jaFDCOJcYf
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:35:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.95/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.95/1.12  % Solved by: fo/fo7.sh
% 0.95/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.95/1.12  % done 886 iterations in 0.641s
% 0.95/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.95/1.12  % SZS output start Refutation
% 0.95/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.95/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.95/1.12  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.95/1.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.95/1.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.95/1.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.95/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.95/1.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.95/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.95/1.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.95/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.95/1.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.95/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.95/1.12  thf(t32_zfmisc_1, conjecture,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.95/1.12       ( k2_tarski @ A @ B ) ))).
% 0.95/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.95/1.12    (~( ![A:$i,B:$i]:
% 0.95/1.12        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.95/1.12          ( k2_tarski @ A @ B ) ) )),
% 0.95/1.12    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.95/1.12  thf('0', plain,
% 0.95/1.12      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.95/1.12         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.95/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.12  thf(l51_zfmisc_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.95/1.12  thf('1', plain,
% 0.95/1.12      (![X61 : $i, X62 : $i]:
% 0.95/1.12         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 0.95/1.12      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.95/1.12  thf('2', plain,
% 0.95/1.12      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.95/1.12         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.95/1.12      inference('demod', [status(thm)], ['0', '1'])).
% 0.95/1.12  thf(t29_zfmisc_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( ( A ) != ( B ) ) =>
% 0.95/1.12       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.95/1.12         ( k2_tarski @ A @ B ) ) ))).
% 0.95/1.12  thf('3', plain,
% 0.95/1.12      (![X65 : $i, X66 : $i]:
% 0.95/1.12         (((k5_xboole_0 @ (k1_tarski @ X65) @ (k1_tarski @ X66))
% 0.95/1.12            = (k2_tarski @ X65 @ X66))
% 0.95/1.12          | ((X65) = (X66)))),
% 0.95/1.12      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.95/1.12  thf(t17_zfmisc_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( ( A ) != ( B ) ) =>
% 0.95/1.12       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.95/1.12  thf('4', plain,
% 0.95/1.12      (![X63 : $i, X64 : $i]:
% 0.95/1.12         ((r1_xboole_0 @ (k1_tarski @ X63) @ (k1_tarski @ X64))
% 0.95/1.12          | ((X63) = (X64)))),
% 0.95/1.12      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.95/1.12  thf(t83_xboole_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.95/1.12  thf('5', plain,
% 0.95/1.12      (![X14 : $i, X15 : $i]:
% 0.95/1.12         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.95/1.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.95/1.12  thf('6', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((X1) = (X0))
% 0.95/1.12          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.95/1.12              = (k1_tarski @ X1)))),
% 0.95/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.95/1.12  thf(t98_xboole_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.95/1.12  thf('7', plain,
% 0.95/1.12      (![X17 : $i, X18 : $i]:
% 0.95/1.12         ((k2_xboole_0 @ X17 @ X18)
% 0.95/1.12           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.95/1.12      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.95/1.12  thf('8', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.95/1.12            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.95/1.12          | ((X0) = (X1)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['6', '7'])).
% 0.95/1.12  thf('9', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.95/1.12            = (k2_tarski @ X1 @ X0))
% 0.95/1.12          | ((X1) = (X0))
% 0.95/1.12          | ((X0) = (X1)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['3', '8'])).
% 0.95/1.12  thf('10', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((X1) = (X0))
% 0.95/1.12          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.95/1.12              = (k2_tarski @ X1 @ X0)))),
% 0.95/1.12      inference('simplify', [status(thm)], ['9'])).
% 0.95/1.12  thf('11', plain,
% 0.95/1.12      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.95/1.12         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.95/1.12      inference('demod', [status(thm)], ['0', '1'])).
% 0.95/1.12  thf('12', plain,
% 0.95/1.12      ((((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))
% 0.95/1.12        | ((sk_A) = (sk_B_1)))),
% 0.95/1.12      inference('sup-', [status(thm)], ['10', '11'])).
% 0.95/1.12  thf('13', plain, (((sk_A) = (sk_B_1))),
% 0.95/1.12      inference('simplify', [status(thm)], ['12'])).
% 0.95/1.12  thf(idempotence_k3_xboole_0, axiom,
% 0.95/1.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.95/1.12  thf('14', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.95/1.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.95/1.12  thf(t100_xboole_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.95/1.12  thf('15', plain,
% 0.95/1.12      (![X8 : $i, X9 : $i]:
% 0.95/1.12         ((k4_xboole_0 @ X8 @ X9)
% 0.95/1.12           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.95/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.95/1.12  thf('16', plain,
% 0.95/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.95/1.12      inference('sup+', [status(thm)], ['14', '15'])).
% 0.95/1.12  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.95/1.12  thf('17', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.95/1.12      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.95/1.12  thf('18', plain,
% 0.95/1.12      (![X14 : $i, X15 : $i]:
% 0.95/1.12         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.95/1.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.95/1.12  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.95/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.95/1.12  thf(t48_xboole_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.95/1.12  thf('20', plain,
% 0.95/1.12      (![X10 : $i, X11 : $i]:
% 0.95/1.12         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.95/1.12           = (k3_xboole_0 @ X10 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.95/1.12  thf('21', plain,
% 0.95/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.95/1.12      inference('sup+', [status(thm)], ['19', '20'])).
% 0.95/1.12  thf('22', plain,
% 0.95/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.95/1.12      inference('sup+', [status(thm)], ['14', '15'])).
% 0.95/1.12  thf('23', plain,
% 0.95/1.12      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.95/1.12      inference('demod', [status(thm)], ['21', '22'])).
% 0.95/1.12  thf('24', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.95/1.12      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.95/1.12  thf(commutativity_k3_xboole_0, axiom,
% 0.95/1.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.95/1.12  thf('25', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.95/1.12  thf(t4_xboole_0, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.95/1.12            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.95/1.12       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.95/1.12            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.95/1.12  thf('26', plain,
% 0.95/1.12      (![X3 : $i, X4 : $i]:
% 0.95/1.12         ((r1_xboole_0 @ X3 @ X4)
% 0.95/1.12          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.95/1.12      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.95/1.12  thf('27', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.95/1.12          | (r1_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('sup+', [status(thm)], ['25', '26'])).
% 0.95/1.12  thf('28', plain,
% 0.95/1.12      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.95/1.12         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.95/1.12          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.95/1.12      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.95/1.12  thf('29', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.95/1.12      inference('sup-', [status(thm)], ['27', '28'])).
% 0.95/1.12  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.95/1.12      inference('sup-', [status(thm)], ['24', '29'])).
% 0.95/1.12  thf('31', plain,
% 0.95/1.12      (![X14 : $i, X15 : $i]:
% 0.95/1.12         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.95/1.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.95/1.12  thf('32', plain,
% 0.95/1.12      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.95/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.95/1.12  thf('33', plain,
% 0.95/1.12      (![X10 : $i, X11 : $i]:
% 0.95/1.12         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.95/1.12           = (k3_xboole_0 @ X10 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.95/1.12  thf('34', plain,
% 0.95/1.12      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.95/1.12      inference('sup+', [status(thm)], ['32', '33'])).
% 0.95/1.12  thf('35', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.95/1.12  thf('36', plain,
% 0.95/1.12      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.95/1.12      inference('sup+', [status(thm)], ['34', '35'])).
% 0.95/1.12  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.95/1.12      inference('demod', [status(thm)], ['23', '36'])).
% 0.95/1.12  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.95/1.12      inference('demod', [status(thm)], ['16', '37'])).
% 0.95/1.12  thf('39', plain,
% 0.95/1.12      (![X17 : $i, X18 : $i]:
% 0.95/1.12         ((k2_xboole_0 @ X17 @ X18)
% 0.95/1.12           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.95/1.12      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.95/1.12  thf('40', plain,
% 0.95/1.12      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.95/1.12      inference('sup+', [status(thm)], ['38', '39'])).
% 0.95/1.12  thf(t5_boole, axiom,
% 0.95/1.12    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.95/1.12  thf('41', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.95/1.12      inference('cnf', [status(esa)], [t5_boole])).
% 0.95/1.12  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.95/1.12      inference('demod', [status(thm)], ['40', '41'])).
% 0.95/1.12  thf('43', plain, (((sk_A) = (sk_B_1))),
% 0.95/1.12      inference('simplify', [status(thm)], ['12'])).
% 0.95/1.12  thf(t69_enumset1, axiom,
% 0.95/1.12    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.95/1.12  thf('44', plain,
% 0.95/1.12      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.95/1.12      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.95/1.12  thf('45', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.95/1.12      inference('demod', [status(thm)], ['2', '13', '42', '43', '44'])).
% 0.95/1.12  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.95/1.12  
% 0.95/1.12  % SZS output end Refutation
% 0.95/1.12  
% 0.95/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
