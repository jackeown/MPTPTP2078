%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9MFMXu35SA

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  553 ( 829 expanded)
%              Number of equality atoms :   39 (  65 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9MFMXu35SA
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 209 iterations in 0.078s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.52  thf(t146_funct_1, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.52         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( v1_relat_1 @ B ) =>
% 0.19/0.52          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.52            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t28_xboole_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (![X2 : $i, X3 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.52  thf('3', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.52  thf(t90_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.19/0.52         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i]:
% 0.19/0.52         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.19/0.52            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.19/0.52          | ~ (v1_relat_1 @ X13))),
% 0.19/0.52      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.19/0.52  thf(t139_funct_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ C ) =>
% 0.19/0.52       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.52         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.52         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.19/0.52            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.19/0.52          | ~ (v1_relat_1 @ X16))),
% 0.19/0.52      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.19/0.52  thf(t169_relat_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ A ) =>
% 0.19/0.52       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X12 : $i]:
% 0.19/0.52         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.19/0.52          | ~ (v1_relat_1 @ X12))),
% 0.19/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X0 @ 
% 0.19/0.52            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.19/0.52            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.52          | ~ (v1_relat_1 @ X1)
% 0.19/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf(dt_k7_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k7_relat_1 @ X8 @ X9)))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X1)
% 0.19/0.52          | ((k3_xboole_0 @ X0 @ 
% 0.19/0.52              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.19/0.52              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf(t17_xboole_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.19/0.52          | ~ (v1_relat_1 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      (![X2 : $i, X3 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X1)
% 0.19/0.52          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.19/0.52              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.52  thf(commutativity_k2_tarski, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.19/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.52  thf(t12_setfam_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X6 : $i, X7 : $i]:
% 0.19/0.52         ((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (k3_xboole_0 @ X6 @ X7))),
% 0.19/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (![X6 : $i, X7 : $i]:
% 0.19/0.52         ((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (k3_xboole_0 @ X6 @ X7))),
% 0.19/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X1)
% 0.19/0.52          | ((k3_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.52              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.52      inference('demod', [status(thm)], ['13', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.19/0.52            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.52          | ~ (v1_relat_1 @ X1)
% 0.19/0.52          | ~ (v1_relat_1 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['4', '19'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X2 : $i, X3 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.19/0.52           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.19/0.52           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.52           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['21', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.19/0.52            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.52          | ~ (v1_relat_1 @ X1)
% 0.19/0.52          | ~ (v1_relat_1 @ X1))),
% 0.19/0.52      inference('demod', [status(thm)], ['20', '27'])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X1)
% 0.19/0.52          | ((k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.19/0.52              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.52         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.19/0.52            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.19/0.52          | ~ (v1_relat_1 @ X16))),
% 0.19/0.52      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.19/0.52  thf(t148_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X10 : $i, X11 : $i]:
% 0.19/0.52         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.19/0.52          | ~ (v1_relat_1 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (![X12 : $i]:
% 0.19/0.52         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.19/0.52          | ~ (v1_relat_1 @ X12))),
% 0.19/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.19/0.52            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.52          | ~ (v1_relat_1 @ X1)
% 0.19/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k7_relat_1 @ X8 @ X9)))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X1)
% 0.19/0.52          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.19/0.52              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.19/0.52            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.52          | ~ (v1_relat_1 @ X1)
% 0.19/0.52          | ~ (v1_relat_1 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['30', '35'])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X1)
% 0.19/0.52          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.19/0.52              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.19/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.19/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.19/0.52           (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.19/0.52          | ~ (v1_relat_1 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['37', '40'])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.19/0.52           (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 0.19/0.52          | ~ (v1_relat_1 @ X0)
% 0.19/0.52          | ~ (v1_relat_1 @ X0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['29', '41'])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X0)
% 0.19/0.52          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.19/0.52             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1))))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.19/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup+', [status(thm)], ['3', '43'])).
% 0.19/0.52  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.52  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
