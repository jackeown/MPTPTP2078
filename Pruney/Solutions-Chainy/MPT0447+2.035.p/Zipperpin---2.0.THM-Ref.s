%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBsvw5SDod

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:57 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  451 ( 882 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
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
    inference('sup+',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X20 @ X19 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
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

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X18 @ X17 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBsvw5SDod
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 1.37/1.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.53  % Solved by: fo/fo7.sh
% 1.37/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.53  % done 1558 iterations in 1.050s
% 1.37/1.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.53  % SZS output start Refutation
% 1.37/1.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.37/1.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.37/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.53  thf(t31_relat_1, conjecture,
% 1.37/1.53    (![A:$i]:
% 1.37/1.53     ( ( v1_relat_1 @ A ) =>
% 1.37/1.53       ( ![B:$i]:
% 1.37/1.53         ( ( v1_relat_1 @ B ) =>
% 1.37/1.53           ( ( r1_tarski @ A @ B ) =>
% 1.37/1.53             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.37/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.53    (~( ![A:$i]:
% 1.37/1.53        ( ( v1_relat_1 @ A ) =>
% 1.37/1.53          ( ![B:$i]:
% 1.37/1.53            ( ( v1_relat_1 @ B ) =>
% 1.37/1.53              ( ( r1_tarski @ A @ B ) =>
% 1.37/1.53                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.37/1.53    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.37/1.53  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.37/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.53  thf(d6_relat_1, axiom,
% 1.37/1.53    (![A:$i]:
% 1.37/1.53     ( ( v1_relat_1 @ A ) =>
% 1.37/1.53       ( ( k3_relat_1 @ A ) =
% 1.37/1.53         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.37/1.53  thf('1', plain,
% 1.37/1.53      (![X16 : $i]:
% 1.37/1.53         (((k3_relat_1 @ X16)
% 1.37/1.53            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 1.37/1.53          | ~ (v1_relat_1 @ X16))),
% 1.37/1.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.37/1.53  thf('2', plain,
% 1.37/1.53      (![X16 : $i]:
% 1.37/1.53         (((k3_relat_1 @ X16)
% 1.37/1.53            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 1.37/1.53          | ~ (v1_relat_1 @ X16))),
% 1.37/1.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.37/1.53  thf(commutativity_k2_xboole_0, axiom,
% 1.37/1.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.37/1.54  thf('3', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf(t7_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.37/1.54  thf('4', plain,
% 1.37/1.54      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 1.37/1.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.37/1.54  thf('5', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['3', '4'])).
% 1.37/1.54  thf('6', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.37/1.54          | ~ (v1_relat_1 @ X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['2', '5'])).
% 1.37/1.54  thf(d10_xboole_0, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.37/1.54  thf('7', plain,
% 1.37/1.54      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.37/1.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.54  thf('8', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.37/1.54      inference('simplify', [status(thm)], ['7'])).
% 1.37/1.54  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf(t8_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i,C:$i]:
% 1.37/1.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.37/1.54       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.37/1.54  thf('10', plain,
% 1.37/1.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.37/1.54         (~ (r1_tarski @ X13 @ X14)
% 1.37/1.54          | ~ (r1_tarski @ X15 @ X14)
% 1.37/1.54          | (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.37/1.54  thf('11', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 1.37/1.54          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.37/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.37/1.54  thf('12', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 1.37/1.54      inference('sup-', [status(thm)], ['8', '11'])).
% 1.37/1.54  thf('13', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['3', '4'])).
% 1.37/1.54  thf('14', plain,
% 1.37/1.54      (![X2 : $i, X4 : $i]:
% 1.37/1.54         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.37/1.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.54  thf('15', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.37/1.54          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.37/1.54      inference('sup-', [status(thm)], ['13', '14'])).
% 1.37/1.54  thf('16', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.37/1.54      inference('sup-', [status(thm)], ['12', '15'])).
% 1.37/1.54  thf(t26_relat_1, axiom,
% 1.37/1.54    (![A:$i]:
% 1.37/1.54     ( ( v1_relat_1 @ A ) =>
% 1.37/1.54       ( ![B:$i]:
% 1.37/1.54         ( ( v1_relat_1 @ B ) =>
% 1.37/1.54           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 1.37/1.54             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.37/1.54  thf('17', plain,
% 1.37/1.54      (![X19 : $i, X20 : $i]:
% 1.37/1.54         (~ (v1_relat_1 @ X19)
% 1.37/1.54          | ((k2_relat_1 @ (k2_xboole_0 @ X20 @ X19))
% 1.37/1.54              = (k2_xboole_0 @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19)))
% 1.37/1.54          | ~ (v1_relat_1 @ X20))),
% 1.37/1.54      inference('cnf', [status(esa)], [t26_relat_1])).
% 1.37/1.54  thf('18', plain,
% 1.37/1.54      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 1.37/1.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.37/1.54  thf(t1_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i,C:$i]:
% 1.37/1.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.37/1.54       ( r1_tarski @ A @ C ) ))).
% 1.37/1.54  thf('19', plain,
% 1.37/1.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.54         (~ (r1_tarski @ X8 @ X9)
% 1.37/1.54          | ~ (r1_tarski @ X9 @ X10)
% 1.37/1.54          | (r1_tarski @ X8 @ X10))),
% 1.37/1.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.37/1.54  thf('20', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.37/1.54      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.54  thf('21', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 1.37/1.54          | ~ (v1_relat_1 @ X1)
% 1.37/1.54          | ~ (v1_relat_1 @ X0)
% 1.37/1.54          | (r1_tarski @ (k2_relat_1 @ X1) @ X2))),
% 1.37/1.54      inference('sup-', [status(thm)], ['17', '20'])).
% 1.37/1.54  thf('22', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.37/1.54          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.37/1.54          | ~ (v1_relat_1 @ sk_B)
% 1.37/1.54          | ~ (v1_relat_1 @ sk_A))),
% 1.37/1.54      inference('sup-', [status(thm)], ['16', '21'])).
% 1.37/1.54  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('25', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.37/1.54          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 1.37/1.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.37/1.54  thf('26', plain,
% 1.37/1.54      ((~ (v1_relat_1 @ sk_B)
% 1.37/1.54        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.37/1.54      inference('sup-', [status(thm)], ['6', '25'])).
% 1.37/1.54  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['26', '27'])).
% 1.37/1.54  thf('29', plain,
% 1.37/1.54      (![X16 : $i]:
% 1.37/1.54         (((k3_relat_1 @ X16)
% 1.37/1.54            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 1.37/1.54          | ~ (v1_relat_1 @ X16))),
% 1.37/1.54      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.37/1.54  thf('30', plain,
% 1.37/1.54      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 1.37/1.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.37/1.54  thf('31', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.37/1.54          | ~ (v1_relat_1 @ X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['29', '30'])).
% 1.37/1.54  thf('32', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.37/1.54      inference('sup-', [status(thm)], ['12', '15'])).
% 1.37/1.54  thf(t13_relat_1, axiom,
% 1.37/1.54    (![A:$i]:
% 1.37/1.54     ( ( v1_relat_1 @ A ) =>
% 1.37/1.54       ( ![B:$i]:
% 1.37/1.54         ( ( v1_relat_1 @ B ) =>
% 1.37/1.54           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 1.37/1.54             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.37/1.54  thf('33', plain,
% 1.37/1.54      (![X17 : $i, X18 : $i]:
% 1.37/1.54         (~ (v1_relat_1 @ X17)
% 1.37/1.54          | ((k1_relat_1 @ (k2_xboole_0 @ X18 @ X17))
% 1.37/1.54              = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k1_relat_1 @ X17)))
% 1.37/1.54          | ~ (v1_relat_1 @ X18))),
% 1.37/1.54      inference('cnf', [status(esa)], [t13_relat_1])).
% 1.37/1.54  thf('34', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.37/1.54      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.54  thf('35', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 1.37/1.54          | ~ (v1_relat_1 @ X1)
% 1.37/1.54          | ~ (v1_relat_1 @ X0)
% 1.37/1.54          | (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 1.37/1.54      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.54  thf('36', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.37/1.54          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.37/1.54          | ~ (v1_relat_1 @ sk_B)
% 1.37/1.54          | ~ (v1_relat_1 @ sk_A))),
% 1.37/1.54      inference('sup-', [status(thm)], ['32', '35'])).
% 1.37/1.54  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('39', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.37/1.54          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 1.37/1.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.37/1.54  thf('40', plain,
% 1.37/1.54      ((~ (v1_relat_1 @ sk_B)
% 1.37/1.54        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.37/1.54      inference('sup-', [status(thm)], ['31', '39'])).
% 1.37/1.54  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('42', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['40', '41'])).
% 1.37/1.54  thf('43', plain,
% 1.37/1.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.37/1.54         (~ (r1_tarski @ X13 @ X14)
% 1.37/1.54          | ~ (r1_tarski @ X15 @ X14)
% 1.37/1.54          | (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.37/1.54  thf('44', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.37/1.54           (k3_relat_1 @ sk_B))
% 1.37/1.54          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.37/1.54      inference('sup-', [status(thm)], ['42', '43'])).
% 1.37/1.54  thf('45', plain,
% 1.37/1.54      ((r1_tarski @ 
% 1.37/1.54        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.37/1.54        (k3_relat_1 @ sk_B))),
% 1.37/1.54      inference('sup-', [status(thm)], ['28', '44'])).
% 1.37/1.54  thf('46', plain,
% 1.37/1.54      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.37/1.54        | ~ (v1_relat_1 @ sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['1', '45'])).
% 1.37/1.54  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('48', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['46', '47'])).
% 1.37/1.54  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 1.37/1.54  
% 1.37/1.54  % SZS output end Refutation
% 1.37/1.54  
% 1.39/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
