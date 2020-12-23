%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVHCrY5Gzj

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 173 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  462 (1314 expanded)
%              Number of equality atoms :   61 ( 168 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('6',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['16','21','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['16','21','32'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    sk_A = sk_C ),
    inference(demod,[status(thm)],['41','42','52'])).

thf('54',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVHCrY5Gzj
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 116 iterations in 0.040s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(t71_xboole_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.21/0.50         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.50       ( ( A ) = ( C ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.50          ( ( A ) = ( C ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t40_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.21/0.50           = (k4_xboole_0 @ X14 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.50         = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.21/0.50           = (k4_xboole_0 @ X14 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(t36_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.50  thf('6', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf(l32_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X7 : $i, X9 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(t48_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.50           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.21/0.50         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.21/0.50           = (k4_xboole_0 @ X14 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.50  thf(t3_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('12', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.21/0.50         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '13', '14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('18', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.50  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.50           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.21/0.50         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d7_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.50  thf('27', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['24', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.50           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.21/0.50         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((sk_C) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '21', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.50           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.50  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['35', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.50           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf('42', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('43', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '21', '32'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X7 : $i, X9 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['43', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.50           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.50  thf('52', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.50  thf('53', plain, (((sk_A) = (sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42', '52'])).
% 0.21/0.50  thf('54', plain, (((sk_A) != (sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
