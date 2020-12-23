%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jKuvVfehFY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:58 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 114 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  468 ( 885 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jKuvVfehFY
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.75  % Solved by: fo/fo7.sh
% 0.50/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.75  % done 535 iterations in 0.291s
% 0.50/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.75  % SZS output start Refutation
% 0.50/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.75  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.50/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.75  thf(t31_relat_1, conjecture,
% 0.50/0.75    (![A:$i]:
% 0.50/0.75     ( ( v1_relat_1 @ A ) =>
% 0.50/0.75       ( ![B:$i]:
% 0.50/0.75         ( ( v1_relat_1 @ B ) =>
% 0.50/0.75           ( ( r1_tarski @ A @ B ) =>
% 0.50/0.75             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.50/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.75    (~( ![A:$i]:
% 0.50/0.75        ( ( v1_relat_1 @ A ) =>
% 0.50/0.75          ( ![B:$i]:
% 0.50/0.75            ( ( v1_relat_1 @ B ) =>
% 0.50/0.75              ( ( r1_tarski @ A @ B ) =>
% 0.50/0.75                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.50/0.75    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 0.50/0.75  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf(d6_relat_1, axiom,
% 0.50/0.75    (![A:$i]:
% 0.50/0.75     ( ( v1_relat_1 @ A ) =>
% 0.50/0.75       ( ( k3_relat_1 @ A ) =
% 0.50/0.75         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.50/0.75  thf('1', plain,
% 0.50/0.75      (![X15 : $i]:
% 0.50/0.75         (((k3_relat_1 @ X15)
% 0.50/0.75            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.50/0.75          | ~ (v1_relat_1 @ X15))),
% 0.50/0.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.50/0.75  thf('2', plain,
% 0.50/0.75      (![X15 : $i]:
% 0.50/0.75         (((k3_relat_1 @ X15)
% 0.50/0.75            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.50/0.75          | ~ (v1_relat_1 @ X15))),
% 0.50/0.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.50/0.75  thf(t7_xboole_1, axiom,
% 0.50/0.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.75  thf('3', plain,
% 0.50/0.75      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.50/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.75  thf('4', plain,
% 0.50/0.75      (![X0 : $i]:
% 0.50/0.75         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.50/0.75          | ~ (v1_relat_1 @ X0))),
% 0.50/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.50/0.75  thf(d10_xboole_0, axiom,
% 0.50/0.75    (![A:$i,B:$i]:
% 0.50/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.75  thf('5', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.50/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.75  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.50/0.75      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.75  thf(t8_xboole_1, axiom,
% 0.50/0.75    (![A:$i,B:$i,C:$i]:
% 0.50/0.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.50/0.75       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.50/0.75  thf('7', plain,
% 0.50/0.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.75         (~ (r1_tarski @ X8 @ X9)
% 0.50/0.75          | ~ (r1_tarski @ X10 @ X9)
% 0.50/0.75          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.50/0.75      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.50/0.75  thf('8', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]:
% 0.50/0.75         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.50/0.75      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.75  thf('9', plain,
% 0.50/0.75      (![X0 : $i]:
% 0.50/0.75         (~ (v1_relat_1 @ X0)
% 0.50/0.75          | (r1_tarski @ 
% 0.50/0.75             (k2_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 0.50/0.75             (k3_relat_1 @ X0)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['4', '8'])).
% 0.50/0.75  thf('10', plain,
% 0.50/0.75      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.50/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.75  thf('11', plain,
% 0.50/0.75      (![X0 : $i, X2 : $i]:
% 0.50/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.75  thf('12', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]:
% 0.50/0.75         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.50/0.75          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.75  thf('13', plain,
% 0.50/0.75      (![X0 : $i]:
% 0.50/0.75         (~ (v1_relat_1 @ X0)
% 0.50/0.75          | ((k2_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.50/0.75              = (k3_relat_1 @ X0)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['9', '12'])).
% 0.50/0.75  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf(t25_relat_1, axiom,
% 0.50/0.75    (![A:$i]:
% 0.50/0.75     ( ( v1_relat_1 @ A ) =>
% 0.50/0.75       ( ![B:$i]:
% 0.50/0.75         ( ( v1_relat_1 @ B ) =>
% 0.50/0.75           ( ( r1_tarski @ A @ B ) =>
% 0.50/0.75             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.50/0.75               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.50/0.75  thf('15', plain,
% 0.50/0.75      (![X16 : $i, X17 : $i]:
% 0.50/0.75         (~ (v1_relat_1 @ X16)
% 0.50/0.75          | (r1_tarski @ (k1_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.50/0.75          | ~ (r1_tarski @ X17 @ X16)
% 0.50/0.75          | ~ (v1_relat_1 @ X17))),
% 0.50/0.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.50/0.75  thf('16', plain,
% 0.50/0.75      ((~ (v1_relat_1 @ sk_A)
% 0.50/0.75        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.50/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.75  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.50/0.75      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.50/0.75  thf(t10_xboole_1, axiom,
% 0.50/0.75    (![A:$i,B:$i,C:$i]:
% 0.50/0.75     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.50/0.75  thf('20', plain,
% 0.50/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.75         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.50/0.75      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.50/0.75  thf('21', plain,
% 0.50/0.75      (![X0 : $i]:
% 0.50/0.75         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.50/0.75          (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.75  thf('22', plain,
% 0.50/0.75      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.50/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.75      inference('sup+', [status(thm)], ['13', '21'])).
% 0.50/0.75  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.50/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.50/0.75  thf('25', plain,
% 0.50/0.75      (![X15 : $i]:
% 0.50/0.75         (((k3_relat_1 @ X15)
% 0.50/0.75            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.50/0.75          | ~ (v1_relat_1 @ X15))),
% 0.50/0.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.50/0.75  thf('26', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('27', plain,
% 0.50/0.75      (![X16 : $i, X17 : $i]:
% 0.50/0.75         (~ (v1_relat_1 @ X16)
% 0.50/0.75          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.50/0.75          | ~ (r1_tarski @ X17 @ X16)
% 0.50/0.75          | ~ (v1_relat_1 @ X17))),
% 0.50/0.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.50/0.75  thf('28', plain,
% 0.50/0.75      ((~ (v1_relat_1 @ sk_A)
% 0.50/0.75        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.50/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.75      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.75  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.50/0.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.50/0.75  thf('32', plain,
% 0.50/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.75         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.50/0.75      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.50/0.75  thf('33', plain,
% 0.50/0.75      (![X0 : $i]:
% 0.50/0.75         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 0.50/0.75          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.75  thf('34', plain,
% 0.50/0.75      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.50/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.75      inference('sup+', [status(thm)], ['25', '33'])).
% 0.50/0.75  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.50/0.75      inference('demod', [status(thm)], ['34', '35'])).
% 0.50/0.75  thf('37', plain,
% 0.50/0.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.75         (~ (r1_tarski @ X8 @ X9)
% 0.50/0.75          | ~ (r1_tarski @ X10 @ X9)
% 0.50/0.75          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.50/0.75      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.50/0.75  thf('38', plain,
% 0.50/0.75      (![X0 : $i]:
% 0.50/0.75         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 0.50/0.75           (k3_relat_1 @ sk_B))
% 0.50/0.75          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.75  thf('39', plain,
% 0.50/0.75      ((r1_tarski @ 
% 0.50/0.75        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 0.50/0.75        (k3_relat_1 @ sk_B))),
% 0.50/0.75      inference('sup-', [status(thm)], ['24', '38'])).
% 0.50/0.75  thf('40', plain,
% 0.50/0.75      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.50/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.75  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.50/0.75      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.75  thf('42', plain,
% 0.50/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.75         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.50/0.75      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.50/0.75  thf('43', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.50/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.75  thf('44', plain,
% 0.50/0.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.75         (~ (r1_tarski @ X8 @ X9)
% 0.50/0.75          | ~ (r1_tarski @ X10 @ X9)
% 0.50/0.75          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.50/0.75      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.50/0.75  thf('45', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.75         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.75          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.75  thf('46', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]:
% 0.50/0.75         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.50/0.75      inference('sup-', [status(thm)], ['40', '45'])).
% 0.50/0.75  thf('47', plain,
% 0.50/0.75      (![X0 : $i, X2 : $i]:
% 0.50/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.75  thf('48', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]:
% 0.50/0.75         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.50/0.75          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 0.50/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.50/0.75  thf('49', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]:
% 0.50/0.75         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.50/0.75      inference('sup-', [status(thm)], ['40', '45'])).
% 0.50/0.75  thf('50', plain,
% 0.50/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.75      inference('demod', [status(thm)], ['48', '49'])).
% 0.50/0.75  thf('51', plain,
% 0.50/0.75      ((r1_tarski @ 
% 0.50/0.75        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 0.50/0.75        (k3_relat_1 @ sk_B))),
% 0.50/0.75      inference('demod', [status(thm)], ['39', '50'])).
% 0.50/0.75  thf('52', plain,
% 0.50/0.75      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.50/0.75        | ~ (v1_relat_1 @ sk_A))),
% 0.50/0.75      inference('sup+', [status(thm)], ['1', '51'])).
% 0.50/0.75  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.75  thf('54', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.50/0.75      inference('demod', [status(thm)], ['52', '53'])).
% 0.50/0.75  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.50/0.75  
% 0.50/0.75  % SZS output end Refutation
% 0.50/0.75  
% 0.58/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
