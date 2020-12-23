%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.er4LOMzeBT

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 108 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  521 ( 824 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relat_1 @ X15 @ ( k8_relat_1 @ X16 @ X17 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t130_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_relat_1])).

thf('1',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X14 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X10 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('11',plain,(
    ! [X14: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X14 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X10 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X10 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','32'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k8_relat_1 @ X13 @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,
    ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X10 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('43',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.er4LOMzeBT
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 63 iterations in 0.056s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(t127_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.20/0.52         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (((k8_relat_1 @ X15 @ (k8_relat_1 @ X16 @ X17))
% 0.20/0.52            = (k8_relat_1 @ (k3_xboole_0 @ X15 @ X16) @ X17))
% 0.20/0.52          | ~ (v1_relat_1 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.20/0.52  thf(t130_relat_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.52         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( v1_relat_1 @ C ) =>
% 0.20/0.52          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.52            ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.20/0.52              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t130_relat_1])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.52         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.20/0.52          != (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.20/0.52         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t71_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('5', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(t126_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X14 : $i]:
% 0.20/0.52         (((k8_relat_1 @ (k2_relat_1 @ X14) @ X14) = (X14))
% 0.20/0.52          | ~ (v1_relat_1 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.52  thf('8', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf(t119_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.20/0.52         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k8_relat_1 @ X11 @ X10))
% 0.20/0.52            = (k3_xboole_0 @ (k2_relat_1 @ X10) @ X11))
% 0.20/0.52          | ~ (v1_relat_1 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X14 : $i]:
% 0.20/0.52         (((k8_relat_1 @ (k2_relat_1 @ X14) @ X14) = (X14))
% 0.20/0.52          | ~ (v1_relat_1 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 0.20/0.52            (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(dt_k8_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X1)
% 0.20/0.52          | ((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 0.20/0.52              (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1)))),
% 0.20/0.52      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k8_relat_1 @ X11 @ X10))
% 0.20/0.52            = (k3_xboole_0 @ (k2_relat_1 @ X10) @ X11))
% 0.20/0.52          | ~ (v1_relat_1 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.52            = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52               (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.52              = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52                 (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1))))),
% 0.20/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k8_relat_1 @ X11 @ X10))
% 0.20/0.52            = (k3_xboole_0 @ (k2_relat_1 @ X10) @ X11))
% 0.20/0.52          | ~ (v1_relat_1 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.52  thf(t116_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X8 @ X9)) @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X1)
% 0.20/0.52          | (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['20', '24'])).
% 0.20/0.52  thf('26', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf(t1_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.52       ( r1_tarski @ A @ C ) ))).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.52          | (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (r1_tarski @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_A)) @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['18', '32'])).
% 0.20/0.52  thf(t125_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.52         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.20/0.52          | ((k8_relat_1 @ X13 @ X12) = (X12))
% 0.20/0.52          | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.52          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.52              = (k8_relat_1 @ sk_A @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.52            = (k8_relat_1 @ sk_A @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((((k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))
% 0.20/0.52          = (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_A)))
% 0.20/0.52        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('40', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (k6_relat_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k8_relat_1 @ X11 @ X10))
% 0.20/0.52            = (k3_xboole_0 @ (k2_relat_1 @ X10) @ X11))
% 0.20/0.52          | ~ (v1_relat_1 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 0.20/0.52          = (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ sk_A)) @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('45', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('46', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('47', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '47'])).
% 0.20/0.52  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
