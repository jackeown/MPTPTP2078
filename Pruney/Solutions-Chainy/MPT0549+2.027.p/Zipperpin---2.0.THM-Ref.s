%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iBA0WeDtkt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 137 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   21
%              Number of atoms          :  503 (1144 expanded)
%              Number of equality atoms :   61 ( 128 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ X9 @ X10 )
        = ( k9_relat_1 @ X9 @ ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('17',plain,
    ( ( ( ( k9_relat_1 @ sk_B @ sk_A )
        = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('29',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('30',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','25','29'])).

thf('31',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['27','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iBA0WeDtkt
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 134 iterations in 0.041s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(t151_relat_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( v1_relat_1 @ B ) =>
% 0.20/0.50          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.50        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.50         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.20/0.50       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf(t149_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X13 : $i]:
% 0.20/0.50         (((k9_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.50        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf(t83_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t48_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.20/0.50          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf(t3_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('10', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf(t2_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.50  thf(t145_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k9_relat_1 @ B @ A ) =
% 0.20/0.50         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (((k9_relat_1 @ X9 @ X10)
% 0.20/0.50            = (k9_relat_1 @ X9 @ (k3_xboole_0 @ (k1_relat_1 @ X9) @ X10)))
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((((k9_relat_1 @ sk_B @ sk_A) = (k9_relat_1 @ sk_B @ k1_xboole_0))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k9_relat_1 @ sk_B @ k1_xboole_0)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.50         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.50         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.50             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.50         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.50             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '21'])).
% 0.20/0.50  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.50         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.50             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.50       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  thf('26', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.20/0.50  thf('27', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.50       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('30', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '25', '29'])).
% 0.20/0.50  thf('31', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.20/0.50  thf(dt_k7_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf(t148_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf(t64_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X14 : $i]:
% 0.20/0.50         (((k2_relat_1 @ X14) != (k1_xboole_0))
% 0.20/0.50          | ((X14) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1)
% 0.20/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ((k9_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '37'])).
% 0.20/0.50  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf(t95_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X15 @ X16) != (k1_xboole_0))
% 0.20/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X15) @ X16)
% 0.20/0.50          | ~ (v1_relat_1 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.50  thf('47', plain, ($false), inference('demod', [status(thm)], ['27', '46'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
