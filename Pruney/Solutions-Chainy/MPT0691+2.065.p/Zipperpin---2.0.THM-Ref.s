%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iMtqN68UFC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 110 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   21
%              Number of atoms          :  553 ( 889 expanded)
%              Number of equality atoms :   48 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k3_xboole_0 @ X21 @ ( k10_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) @ X13 )
        = ( k9_relat_1 @ X15 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('28',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('30',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iMtqN68UFC
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 62 iterations in 0.083s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(t146_funct_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( v1_relat_1 @ B ) =>
% 0.21/0.53          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t139_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         (((k10_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X23)
% 0.21/0.53            = (k3_xboole_0 @ X21 @ (k10_relat_1 @ X22 @ X23)))
% 0.21/0.53          | ~ (v1_relat_1 @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.53  thf(dt_k7_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf(t162_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.53           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.53             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.53          | ((k9_relat_1 @ (k7_relat_1 @ X15 @ X14) @ X13)
% 0.21/0.53              = (k9_relat_1 @ X15 @ X13))
% 0.21/0.53          | ~ (v1_relat_1 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X1)
% 0.21/0.53          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.21/0.53              = (k9_relat_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf(t90_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.53         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 0.21/0.53            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.21/0.53          | ~ (v1_relat_1 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.53  thf('8', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t91_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.21/0.53          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 0.21/0.53          | ~ (v1_relat_1 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '12'])).
% 0.21/0.53  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 0.21/0.53            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.21/0.53          | ~ (v1_relat_1 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.53  thf(t146_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 0.21/0.53          | ~ (v1_relat_1 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.53            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.53            = (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X1)
% 0.21/0.53          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.53              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.53              = (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.21/0.53      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.53          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['15', '20'])).
% 0.21/0.53  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.53         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '23'])).
% 0.21/0.53  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf(t169_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X16 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 0.21/0.53          | ~ (v1_relat_1 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53          = (sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.21/0.53            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '30'])).
% 0.21/0.53  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53         = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((((k3_xboole_0 @ sk_A @ 
% 0.21/0.53          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '33'])).
% 0.21/0.53  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf(t100_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ X7)
% 0.21/0.53           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf(t28_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('41', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ X7)
% 0.21/0.53           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf(l32_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X3 : $i, X5 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['43', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['38', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.53  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
