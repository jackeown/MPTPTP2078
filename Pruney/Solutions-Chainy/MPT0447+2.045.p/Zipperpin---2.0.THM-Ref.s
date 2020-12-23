%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kdeifg5B0e

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:59 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 113 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  436 ( 872 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X21 @ X20 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X21 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X19 @ X18 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kdeifg5B0e
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 991 iterations in 0.514s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.77/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.96  thf(t31_relat_1, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v1_relat_1 @ B ) =>
% 0.77/0.96           ( ( r1_tarski @ A @ B ) =>
% 0.77/0.96             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( v1_relat_1 @ A ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( v1_relat_1 @ B ) =>
% 0.77/0.96              ( ( r1_tarski @ A @ B ) =>
% 0.77/0.96                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 0.77/0.96  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(d6_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ( k3_relat_1 @ A ) =
% 0.77/0.96         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (![X17 : $i]:
% 0.77/0.96         (((k3_relat_1 @ X17)
% 0.77/0.96            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.77/0.96          | ~ (v1_relat_1 @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (![X17 : $i]:
% 0.77/0.96         (((k3_relat_1 @ X17)
% 0.77/0.96            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.77/0.96          | ~ (v1_relat_1 @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.77/0.96  thf(d10_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.96  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.77/0.96      inference('simplify', [status(thm)], ['3'])).
% 0.77/0.96  thf(t10_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['2', '6'])).
% 0.77/0.96  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.77/0.96      inference('simplify', [status(thm)], ['3'])).
% 0.77/0.96  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t8_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.77/0.96       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X14 @ X15)
% 0.77/0.96          | ~ (r1_tarski @ X16 @ X15)
% 0.77/0.96          | (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.77/0.96  thf('12', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.77/0.96      inference('sup-', [status(thm)], ['8', '11'])).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      (![X0 : $i, X2 : $i]:
% 0.77/0.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.77/0.96          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.96  thf('16', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['12', '15'])).
% 0.77/0.96  thf(t26_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v1_relat_1 @ B ) =>
% 0.77/0.96           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.77/0.96             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      (![X20 : $i, X21 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X20)
% 0.77/0.96          | ((k2_relat_1 @ (k2_xboole_0 @ X21 @ X20))
% 0.77/0.96              = (k2_xboole_0 @ (k2_relat_1 @ X21) @ (k2_relat_1 @ X20)))
% 0.77/0.96          | ~ (v1_relat_1 @ X21))),
% 0.77/0.96      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.77/0.96  thf(t11_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.77/0.96  thf('18', plain,
% 0.77/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.96         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (r1_tarski @ (k2_relat_1 @ X1) @ X2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.77/0.96          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['16', '19'])).
% 0.77/0.96  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.77/0.96          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '23'])).
% 0.77/0.96  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['24', '25'])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      (![X17 : $i]:
% 0.77/0.96         (((k3_relat_1 @ X17)
% 0.77/0.96            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.77/0.96          | ~ (v1_relat_1 @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.77/0.96  thf(t7_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.77/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['27', '28'])).
% 0.77/0.96  thf('30', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['12', '15'])).
% 0.77/0.96  thf(t13_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v1_relat_1 @ B ) =>
% 0.77/0.96           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.77/0.96             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X18)
% 0.77/0.96          | ((k1_relat_1 @ (k2_xboole_0 @ X19 @ X18))
% 0.77/0.96              = (k2_xboole_0 @ (k1_relat_1 @ X19) @ (k1_relat_1 @ X18)))
% 0.77/0.96          | ~ (v1_relat_1 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t13_relat_1])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.96         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['30', '33'])).
% 0.77/0.96  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '37'])).
% 0.77/0.96  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['38', '39'])).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X14 @ X15)
% 0.77/0.96          | ~ (r1_tarski @ X16 @ X15)
% 0.77/0.96          | (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 0.77/0.96           (k3_relat_1 @ sk_B))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['40', '41'])).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      ((r1_tarski @ 
% 0.77/0.96        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 0.77/0.96        (k3_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['26', '42'])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['1', '43'])).
% 0.77/0.96  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('46', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.96  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
