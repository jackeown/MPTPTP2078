%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Arg4QwAQEY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:08 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 112 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  501 ( 827 expanded)
%              Number of equality atoms :   47 (  78 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('5',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('31',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Arg4QwAQEY
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 192 iterations in 0.092s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(t95_relat_1, conjecture,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) =>
% 0.35/0.55       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i]:
% 0.35/0.55        ( ( v1_relat_1 @ B ) =>
% 0.35/0.55          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.55            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.35/0.55        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.35/0.55       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.35/0.55        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.35/0.55         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf(t90_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) =>
% 0.35/0.55       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.35/0.55         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.35/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.35/0.55          | ~ (v1_relat_1 @ X13))),
% 0.35/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (((((k1_relat_1 @ k1_xboole_0)
% 0.35/0.55           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.55         | ~ (v1_relat_1 @ sk_B)))
% 0.35/0.55         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.55  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((((k1_relat_1 @ k1_xboole_0)
% 0.35/0.55          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.35/0.55         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.55  thf(d7_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.35/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X0 : $i, X2 : $i]:
% 0.35/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.35/0.55         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.35/0.55         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf(t88_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i]:
% 0.35/0.55         ((r1_tarski @ (k7_relat_1 @ X11 @ X12) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.35/0.55      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.35/0.55  thf(t3_xboole_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.55          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.55  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t2_boole, axiom,
% 0.35/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.55  thf(fc1_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (![X8 : $i, X9 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['12', '17'])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.35/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.35/0.55          | ~ (v1_relat_1 @ X13))),
% 0.35/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k1_relat_1 @ k1_xboole_0)
% 0.35/0.55            = (k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((k1_relat_1 @ k1_xboole_0)
% 0.35/0.55           = (k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.55  thf('24', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.55         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.35/0.55         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('demod', [status(thm)], ['9', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.55         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.55         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.35/0.55       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.35/0.55       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf(dt_k7_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.35/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.35/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.35/0.55          | ~ (v1_relat_1 @ X13))),
% 0.35/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.35/0.55  thf(fc8_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.35/0.55       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (![X10 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ (k1_relat_1 @ X10))
% 0.35/0.55          | ~ (v1_relat_1 @ X10)
% 0.35/0.55          | (v1_xboole_0 @ X10))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ X1)
% 0.35/0.55          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.55         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.35/0.55         | ~ (v1_relat_1 @ sk_B)))
% 0.35/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.35/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.55  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.55  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.35/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.35/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['30', '40'])).
% 0.35/0.55  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      (((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.55  thf(l13_xboole_0, axiom,
% 0.35/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.55      inference('sup+', [status(thm)], ['44', '45'])).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.35/0.55         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (((X0) != (k1_xboole_0))
% 0.35/0.55           | ~ (v1_xboole_0 @ X0)
% 0.35/0.55           | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.35/0.55         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      (((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.35/0.55         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.35/0.55         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.35/0.55  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.55         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.55      inference('simplify_reflect+', [status(thm)], ['49', '50'])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.35/0.55       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['43', '51'])).
% 0.35/0.55  thf('53', plain, ($false),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['1', '28', '29', '52'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
