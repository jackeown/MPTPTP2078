%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V5VYoO1DWz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 121 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 ( 930 expanded)
%              Number of equality atoms :   61 ( 120 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
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
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
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

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('18',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','19','36','37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V5VYoO1DWz
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.74/1.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.96  % Solved by: fo/fo7.sh
% 1.74/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.96  % done 2302 iterations in 1.510s
% 1.74/1.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.96  % SZS output start Refutation
% 1.74/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.74/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.74/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(t32_zfmisc_1, conjecture,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.74/1.96       ( k2_tarski @ A @ B ) ))).
% 1.74/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.96    (~( ![A:$i,B:$i]:
% 1.74/1.96        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.74/1.96          ( k2_tarski @ A @ B ) ) )),
% 1.74/1.96    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 1.74/1.96  thf('0', plain,
% 1.74/1.96      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.74/1.96         != (k2_tarski @ sk_A @ sk_B))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(l51_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.74/1.96  thf('1', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('2', plain,
% 1.74/1.96      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.74/1.96         != (k2_tarski @ sk_A @ sk_B))),
% 1.74/1.96      inference('demod', [status(thm)], ['0', '1'])).
% 1.74/1.96  thf(t29_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ( A ) != ( B ) ) =>
% 1.74/1.96       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.74/1.96         ( k2_tarski @ A @ B ) ) ))).
% 1.74/1.96  thf('3', plain,
% 1.74/1.96      (![X65 : $i, X66 : $i]:
% 1.74/1.96         (((k5_xboole_0 @ (k1_tarski @ X65) @ (k1_tarski @ X66))
% 1.74/1.96            = (k2_tarski @ X65 @ X66))
% 1.74/1.96          | ((X65) = (X66)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 1.74/1.96  thf(t17_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ( A ) != ( B ) ) =>
% 1.74/1.96       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.74/1.96  thf('4', plain,
% 1.74/1.96      (![X63 : $i, X64 : $i]:
% 1.74/1.96         ((r1_xboole_0 @ (k1_tarski @ X63) @ (k1_tarski @ X64))
% 1.74/1.96          | ((X63) = (X64)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 1.74/1.96  thf(t83_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.74/1.96  thf('5', plain,
% 1.74/1.96      (![X11 : $i, X12 : $i]:
% 1.74/1.96         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 1.74/1.96      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.74/1.96  thf('6', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((X1) = (X0))
% 1.74/1.96          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.74/1.96              = (k1_tarski @ X1)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['4', '5'])).
% 1.74/1.96  thf(commutativity_k3_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.74/1.96  thf('7', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.74/1.96  thf(t94_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k2_xboole_0 @ A @ B ) =
% 1.74/1.96       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.96  thf('8', plain,
% 1.74/1.96      (![X17 : $i, X18 : $i]:
% 1.74/1.96         ((k2_xboole_0 @ X17 @ X18)
% 1.74/1.96           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 1.74/1.96              (k3_xboole_0 @ X17 @ X18)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.74/1.96  thf(t91_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.74/1.96       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.74/1.96  thf('9', plain,
% 1.74/1.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.74/1.96           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.96  thf('10', plain,
% 1.74/1.96      (![X17 : $i, X18 : $i]:
% 1.74/1.96         ((k2_xboole_0 @ X17 @ X18)
% 1.74/1.96           = (k5_xboole_0 @ X17 @ 
% 1.74/1.96              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 1.74/1.96      inference('demod', [status(thm)], ['8', '9'])).
% 1.74/1.96  thf('11', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k2_xboole_0 @ X0 @ X1)
% 1.74/1.96           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['7', '10'])).
% 1.74/1.96  thf(t100_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.96  thf('12', plain,
% 1.74/1.96      (![X3 : $i, X4 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X3 @ X4)
% 1.74/1.96           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('13', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k2_xboole_0 @ X0 @ X1)
% 1.74/1.96           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['11', '12'])).
% 1.74/1.96  thf('14', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.74/1.96            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.74/1.96          | ((X0) = (X1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['6', '13'])).
% 1.74/1.96  thf('15', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.74/1.96            = (k2_tarski @ X1 @ X0))
% 1.74/1.96          | ((X1) = (X0))
% 1.74/1.96          | ((X0) = (X1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['3', '14'])).
% 1.74/1.96  thf('16', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((X1) = (X0))
% 1.74/1.96          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.74/1.96              = (k2_tarski @ X1 @ X0)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['15'])).
% 1.74/1.96  thf('17', plain,
% 1.74/1.96      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.74/1.96         != (k2_tarski @ sk_A @ sk_B))),
% 1.74/1.96      inference('demod', [status(thm)], ['0', '1'])).
% 1.74/1.96  thf('18', plain,
% 1.74/1.96      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.74/1.96        | ((sk_A) = (sk_B)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['16', '17'])).
% 1.74/1.96  thf('19', plain, (((sk_A) = (sk_B))),
% 1.74/1.96      inference('simplify', [status(thm)], ['18'])).
% 1.74/1.96  thf('20', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k2_xboole_0 @ X0 @ X1)
% 1.74/1.96           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['11', '12'])).
% 1.74/1.96  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.74/1.96  thf('21', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.74/1.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.74/1.96  thf(t28_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.74/1.96  thf('22', plain,
% 1.74/1.96      (![X5 : $i, X6 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 1.74/1.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.74/1.96  thf('23', plain,
% 1.74/1.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['21', '22'])).
% 1.74/1.96  thf('24', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.74/1.96  thf('25', plain,
% 1.74/1.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['23', '24'])).
% 1.74/1.96  thf('26', plain,
% 1.74/1.96      (![X3 : $i, X4 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X3 @ X4)
% 1.74/1.96           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('27', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['25', '26'])).
% 1.74/1.96  thf(t5_boole, axiom,
% 1.74/1.96    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.74/1.96  thf('28', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['27', '28'])).
% 1.74/1.96  thf(t48_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.74/1.96  thf('30', plain,
% 1.74/1.96      (![X8 : $i, X9 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.74/1.96           = (k3_xboole_0 @ X8 @ X9))),
% 1.74/1.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.74/1.96  thf('31', plain,
% 1.74/1.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['29', '30'])).
% 1.74/1.96  thf('32', plain,
% 1.74/1.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['23', '24'])).
% 1.74/1.96  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['31', '32'])).
% 1.74/1.96  thf('34', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('35', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 1.74/1.96      inference('sup+', [status(thm)], ['33', '34'])).
% 1.74/1.96  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['20', '35'])).
% 1.74/1.96  thf('37', plain, (((sk_A) = (sk_B))),
% 1.74/1.96      inference('simplify', [status(thm)], ['18'])).
% 1.74/1.96  thf(t69_enumset1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.74/1.96  thf('38', plain,
% 1.74/1.96      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 1.74/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.96  thf('39', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 1.74/1.96      inference('demod', [status(thm)], ['2', '19', '36', '37', '38'])).
% 1.74/1.96  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 1.74/1.96  
% 1.74/1.96  % SZS output end Refutation
% 1.74/1.96  
% 1.74/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
