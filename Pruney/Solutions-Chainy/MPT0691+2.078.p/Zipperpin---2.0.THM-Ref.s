%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s8ZLIyB1QV

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 129 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   21
%              Number of atoms          :  540 (1106 expanded)
%              Number of equality atoms :   44 (  59 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('10',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('22',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('24',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('26',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('38',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s8ZLIyB1QV
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 65 iterations in 0.039s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.49  thf(t146_funct_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.49         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( v1_relat_1 @ B ) =>
% 0.19/0.49          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.49            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t148_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i]:
% 0.19/0.49         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.19/0.49          | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.49  thf(dt_k7_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.49  thf('4', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t91_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.49         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.19/0.49          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 0.19/0.49          | ~ (v1_relat_1 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.49        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf(t98_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X14 : $i]:
% 0.19/0.49         (((k7_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (X14))
% 0.19/0.49          | ~ (v1_relat_1 @ X14))),
% 0.19/0.49      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49          = (k7_relat_1 @ sk_B @ sk_A))
% 0.19/0.49        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.49        | ((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49            = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '10'])).
% 0.19/0.49  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i]:
% 0.19/0.49         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.19/0.49          | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.49  thf(t169_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X11 : $i]:
% 0.19/0.49         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 0.19/0.49          | ~ (v1_relat_1 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.19/0.49            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.49          | ~ (v1_relat_1 @ X1)
% 0.19/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X1)
% 0.19/0.49          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.19/0.49              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.19/0.49          (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))
% 0.19/0.49          = (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)))
% 0.19/0.49        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['13', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('21', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.19/0.49          (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)) = (sk_A))
% 0.19/0.49        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.49  thf('24', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf(t146_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X8 : $i]:
% 0.19/0.49         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 0.19/0.49          | ~ (v1_relat_1 @ X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.19/0.49        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.49        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.49  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.19/0.49          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.19/0.49        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.49        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.19/0.49            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '30'])).
% 0.19/0.49  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.19/0.49         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.19/0.49          = (sk_A))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['1', '33'])).
% 0.19/0.49  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.19/0.49         = (sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf(t139_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.49         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.49         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.19/0.49            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.19/0.49          | ~ (v1_relat_1 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((((sk_A)
% 0.19/0.49          = (k3_xboole_0 @ sk_A @ 
% 0.19/0.49             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (((sk_A)
% 0.19/0.49         = (k3_xboole_0 @ sk_A @ 
% 0.19/0.49            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf(t100_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X3 @ X4)
% 0.19/0.49           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.19/0.49         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['40', '41'])).
% 0.19/0.49  thf(t92_xboole_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('43', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.19/0.49         = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf(l32_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.49        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.49  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
