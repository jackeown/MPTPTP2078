%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aTTuG2xZdQ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:52 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 123 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  439 (1045 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t30_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('43',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X15 @ X14 )
      | ~ ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['19','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aTTuG2xZdQ
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.61/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.78  % Solved by: fo/fo7.sh
% 0.61/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.78  % done 685 iterations in 0.323s
% 0.61/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.78  % SZS output start Refutation
% 0.61/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.78  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.61/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.61/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.78  thf(t30_relat_1, conjecture,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( v1_relat_1 @ C ) =>
% 0.61/0.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.61/0.78         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.61/0.78           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.61/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.78        ( ( v1_relat_1 @ C ) =>
% 0.61/0.78          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.61/0.78            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.61/0.78              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.61/0.78    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.61/0.78  thf('0', plain,
% 0.61/0.78      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.61/0.78        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('1', plain,
% 0.61/0.78      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))
% 0.61/0.78         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))))),
% 0.61/0.78      inference('split', [status(esa)], ['0'])).
% 0.61/0.78  thf(d6_relat_1, axiom,
% 0.61/0.78    (![A:$i]:
% 0.61/0.78     ( ( v1_relat_1 @ A ) =>
% 0.61/0.78       ( ( k3_relat_1 @ A ) =
% 0.61/0.78         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.61/0.78  thf('2', plain,
% 0.61/0.78      (![X17 : $i]:
% 0.61/0.78         (((k3_relat_1 @ X17)
% 0.61/0.78            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.61/0.78          | ~ (v1_relat_1 @ X17))),
% 0.61/0.78      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.61/0.78  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf(t20_relat_1, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( v1_relat_1 @ C ) =>
% 0.61/0.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.61/0.78         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.61/0.78           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.61/0.78  thf('4', plain,
% 0.61/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.78         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.61/0.78          | (r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.61/0.78          | ~ (v1_relat_1 @ X20))),
% 0.61/0.78      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.61/0.78  thf('5', plain,
% 0.61/0.78      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.78  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('7', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['5', '6'])).
% 0.61/0.78  thf(t7_xboole_1, axiom,
% 0.61/0.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.78  thf('8', plain,
% 0.61/0.78      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.61/0.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.78  thf(d3_tarski, axiom,
% 0.61/0.78    (![A:$i,B:$i]:
% 0.61/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.78  thf('9', plain,
% 0.61/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.78          | (r2_hidden @ X0 @ X2)
% 0.61/0.78          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.78  thf('10', plain,
% 0.61/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.78         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.78  thf('11', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (r2_hidden @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.61/0.78      inference('sup-', [status(thm)], ['7', '10'])).
% 0.61/0.78  thf('12', plain,
% 0.61/0.78      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('sup+', [status(thm)], ['2', '11'])).
% 0.61/0.78  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('14', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['12', '13'])).
% 0.61/0.78  thf('15', plain,
% 0.61/0.78      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))
% 0.61/0.78         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))))),
% 0.61/0.78      inference('split', [status(esa)], ['0'])).
% 0.61/0.78  thf('16', plain, (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.78  thf('17', plain,
% 0.61/0.78      (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))) | 
% 0.61/0.78       ~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('split', [status(esa)], ['0'])).
% 0.61/0.78  thf('18', plain, (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.61/0.78  thf('19', plain, (~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.61/0.78  thf('20', plain,
% 0.61/0.78      (![X17 : $i]:
% 0.61/0.78         (((k3_relat_1 @ X17)
% 0.61/0.78            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.61/0.78          | ~ (v1_relat_1 @ X17))),
% 0.61/0.78      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.61/0.78  thf('21', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('22', plain,
% 0.61/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.78         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.61/0.78          | (r2_hidden @ X19 @ (k2_relat_1 @ X20))
% 0.61/0.78          | ~ (v1_relat_1 @ X20))),
% 0.61/0.78      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.61/0.78  thf('23', plain,
% 0.61/0.78      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.78  thf('24', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('25', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['23', '24'])).
% 0.61/0.78  thf('26', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['23', '24'])).
% 0.61/0.78  thf(t38_zfmisc_1, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.61/0.78       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.61/0.78  thf('27', plain,
% 0.61/0.78      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.61/0.78         ((r1_tarski @ (k2_tarski @ X13 @ X15) @ X16)
% 0.61/0.78          | ~ (r2_hidden @ X15 @ X16)
% 0.61/0.78          | ~ (r2_hidden @ X13 @ X16))),
% 0.61/0.78      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.61/0.78  thf('28', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.61/0.78          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.61/0.78  thf('29', plain,
% 0.61/0.78      ((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ (k2_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['25', '28'])).
% 0.61/0.78  thf(t69_enumset1, axiom,
% 0.61/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.78  thf('30', plain,
% 0.61/0.78      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.61/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.78  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k2_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['29', '30'])).
% 0.61/0.78  thf('32', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['5', '6'])).
% 0.61/0.78  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['5', '6'])).
% 0.61/0.78  thf('34', plain,
% 0.61/0.78      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.61/0.78         ((r1_tarski @ (k2_tarski @ X13 @ X15) @ X16)
% 0.61/0.78          | ~ (r2_hidden @ X15 @ X16)
% 0.61/0.78          | ~ (r2_hidden @ X13 @ X16))),
% 0.61/0.78      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.61/0.78  thf('35', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.61/0.78          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ (k1_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['33', '34'])).
% 0.61/0.78  thf('36', plain,
% 0.61/0.78      ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['32', '35'])).
% 0.61/0.78  thf('37', plain,
% 0.61/0.78      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.61/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.78  thf('38', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['36', '37'])).
% 0.61/0.78  thf(t13_xboole_1, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.61/0.78       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 0.61/0.78  thf('39', plain,
% 0.61/0.78      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.61/0.78         (~ (r1_tarski @ X4 @ X5)
% 0.61/0.78          | ~ (r1_tarski @ X6 @ X7)
% 0.61/0.78          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ (k2_xboole_0 @ X5 @ X7)))),
% 0.61/0.78      inference('cnf', [status(esa)], [t13_xboole_1])).
% 0.61/0.78  thf('40', plain,
% 0.61/0.78      (![X0 : $i, X1 : $i]:
% 0.61/0.78         ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X1) @ 
% 0.61/0.78           (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0))
% 0.61/0.78          | ~ (r1_tarski @ X1 @ X0))),
% 0.61/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.78  thf('41', plain,
% 0.61/0.78      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.61/0.78        (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['31', '40'])).
% 0.61/0.78  thf(t41_enumset1, axiom,
% 0.61/0.78    (![A:$i,B:$i]:
% 0.61/0.78     ( ( k2_tarski @ A @ B ) =
% 0.61/0.78       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.61/0.78  thf('42', plain,
% 0.61/0.78      (![X10 : $i, X11 : $i]:
% 0.61/0.78         ((k2_tarski @ X10 @ X11)
% 0.61/0.78           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.61/0.78      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.61/0.78  thf('43', plain,
% 0.61/0.78      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.61/0.78        (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.61/0.78      inference('demod', [status(thm)], ['41', '42'])).
% 0.61/0.78  thf('44', plain,
% 0.61/0.78      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k3_relat_1 @ sk_C_1))
% 0.61/0.78        | ~ (v1_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('sup+', [status(thm)], ['20', '43'])).
% 0.61/0.78  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('46', plain,
% 0.61/0.78      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k3_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['44', '45'])).
% 0.61/0.78  thf('47', plain,
% 0.61/0.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.61/0.78         ((r2_hidden @ X15 @ X14)
% 0.61/0.78          | ~ (r1_tarski @ (k2_tarski @ X13 @ X15) @ X14))),
% 0.61/0.78      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.61/0.78  thf('48', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.78  thf('49', plain, ($false), inference('demod', [status(thm)], ['19', '48'])).
% 0.61/0.78  
% 0.61/0.78  % SZS output end Refutation
% 0.61/0.78  
% 0.61/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
