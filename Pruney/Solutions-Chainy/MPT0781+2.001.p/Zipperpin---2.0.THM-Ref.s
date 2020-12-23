%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWEQXOVFXA

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  349 ( 467 expanded)
%              Number of equality atoms :   39 (  57 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k3_relat_1 @ X9 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','14'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k8_relat_1 @ X11 @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( ( k3_relat_1 @ X9 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_wellord1 @ X15 @ X14 )
        = ( k8_relat_1 @ X14 @ ( k7_relat_1 @ X15 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t30_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t30_wellord1])).

thf('28',plain,(
    ( k2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWEQXOVFXA
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:23 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 38 iterations in 0.020s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.49  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.49  thf(d6_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k3_relat_1 @ A ) =
% 0.22/0.49         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X9 : $i]:
% 0.22/0.49         (((k3_relat_1 @ X9)
% 0.22/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X9)))
% 0.22/0.49          | ~ (v1_relat_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.49  thf(commutativity_k2_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.49  thf(t93_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf(t46_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.49  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.22/0.49  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (o_0_0_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(t37_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.49  thf('10', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (o_0_0_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.22/0.49          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['5', '13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '14'])).
% 0.22/0.49  thf(t125_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.49         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.22/0.49          | ((k8_relat_1 @ X11 @ X10) = (X10))
% 0.22/0.49          | ~ (v1_relat_1 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X9 : $i]:
% 0.22/0.49         (((k3_relat_1 @ X9)
% 0.22/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X9)))
% 0.22/0.49          | ~ (v1_relat_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf(t97_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.49         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.22/0.49          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.22/0.49          | ~ (v1_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.49  thf(t18_wellord1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         (((k2_wellord1 @ X15 @ X14)
% 0.22/0.49            = (k8_relat_1 @ X14 @ (k7_relat_1 @ X15 @ X14)))
% 0.22/0.49          | ~ (v1_relat_1 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.49            = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.49              = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.49  thf(t30_wellord1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( v1_relat_1 @ A ) =>
% 0.22/0.49          ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t30_wellord1])).
% 0.22/0.49  thf('28', plain, (((k2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)) != (sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain, (((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('32', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '31'])).
% 0.22/0.49  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain, (((sk_A) != (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
