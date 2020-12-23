%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LHOjp92LHU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:19 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 105 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  565 ( 830 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LHOjp92LHU
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:58:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 1634 iterations in 0.794s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.05/1.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.05/1.25  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.05/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.25  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.25  thf(t146_funct_1, conjecture,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( v1_relat_1 @ B ) =>
% 1.05/1.25       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.05/1.25         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i,B:$i]:
% 1.05/1.25        ( ( v1_relat_1 @ B ) =>
% 1.05/1.25          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.05/1.25            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.05/1.25  thf('0', plain,
% 1.05/1.25      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(d10_xboole_0, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.25  thf('1', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.25  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.25      inference('simplify', [status(thm)], ['1'])).
% 1.05/1.25  thf('3', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t19_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.05/1.25       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.05/1.25  thf('4', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.25         (~ (r1_tarski @ X8 @ X9)
% 1.05/1.25          | ~ (r1_tarski @ X8 @ X10)
% 1.05/1.25          | (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((r1_tarski @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))
% 1.05/1.25          | ~ (r1_tarski @ sk_A @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      ((r1_tarski @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['2', '5'])).
% 1.05/1.25  thf(commutativity_k2_tarski, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      (![X11 : $i, X12 : $i]:
% 1.05/1.25         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.05/1.25  thf(t12_setfam_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i]:
% 1.05/1.25         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 1.05/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['7', '8'])).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i]:
% 1.05/1.25         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 1.05/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['9', '10'])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.05/1.25      inference('demod', [status(thm)], ['6', '11'])).
% 1.05/1.25  thf(t17_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.05/1.25  thf('13', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.05/1.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.05/1.26  thf('14', plain,
% 1.05/1.26      (![X0 : $i, X2 : $i]:
% 1.05/1.26         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.05/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.26  thf('15', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.05/1.26          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.26  thf('16', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['12', '15'])).
% 1.05/1.26  thf('17', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['9', '10'])).
% 1.05/1.26  thf(t90_relat_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ B ) =>
% 1.05/1.26       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.05/1.26         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.05/1.26  thf('18', plain,
% 1.05/1.26      (![X20 : $i, X21 : $i]:
% 1.05/1.26         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 1.05/1.26            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 1.05/1.26          | ~ (v1_relat_1 @ X20))),
% 1.05/1.26      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.05/1.26  thf(t139_funct_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ C ) =>
% 1.05/1.26       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.05/1.26         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.05/1.26  thf('19', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 1.05/1.26            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 1.05/1.26          | ~ (v1_relat_1 @ X23))),
% 1.05/1.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.05/1.26  thf(t169_relat_1, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ A ) =>
% 1.05/1.26       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.05/1.26  thf('20', plain,
% 1.05/1.26      (![X19 : $i]:
% 1.05/1.26         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 1.05/1.26          | ~ (v1_relat_1 @ X19))),
% 1.05/1.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.05/1.26  thf('21', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X0 @ 
% 1.05/1.26            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.05/1.26            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['19', '20'])).
% 1.05/1.26  thf(dt_k7_relat_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.05/1.26  thf('22', plain,
% 1.05/1.26      (![X15 : $i, X16 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.05/1.26  thf('23', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ((k3_xboole_0 @ X0 @ 
% 1.05/1.26              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.05/1.26              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.05/1.26      inference('clc', [status(thm)], ['21', '22'])).
% 1.05/1.26  thf('24', plain,
% 1.05/1.26      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.05/1.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.05/1.26  thf('25', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['23', '24'])).
% 1.05/1.26  thf('26', plain,
% 1.05/1.26      (![X0 : $i, X2 : $i]:
% 1.05/1.26         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.05/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.26  thf('27', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['25', '26'])).
% 1.05/1.26  thf('28', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['18', '27'])).
% 1.05/1.26  thf('29', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['28'])).
% 1.05/1.26  thf('30', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | ((X1) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['17', '29'])).
% 1.05/1.26  thf('31', plain,
% 1.05/1.26      ((~ (r1_tarski @ sk_A @ sk_A)
% 1.05/1.26        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.05/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.05/1.26      inference('sup-', [status(thm)], ['16', '30'])).
% 1.05/1.26  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.26      inference('simplify', [status(thm)], ['1'])).
% 1.05/1.26  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('34', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.05/1.26      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.05/1.26  thf('35', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 1.05/1.26            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 1.05/1.26          | ~ (v1_relat_1 @ X23))),
% 1.05/1.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.05/1.26  thf(t148_relat_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ B ) =>
% 1.05/1.26       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.05/1.26  thf('36', plain,
% 1.05/1.26      (![X17 : $i, X18 : $i]:
% 1.05/1.26         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 1.05/1.26          | ~ (v1_relat_1 @ X17))),
% 1.05/1.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.05/1.26  thf('37', plain,
% 1.05/1.26      (![X19 : $i]:
% 1.05/1.26         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 1.05/1.26          | ~ (v1_relat_1 @ X19))),
% 1.05/1.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.05/1.26  thf('38', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.05/1.26            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('39', plain,
% 1.05/1.26      (![X15 : $i, X16 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.05/1.26  thf('40', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.05/1.26              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.05/1.26      inference('clc', [status(thm)], ['38', '39'])).
% 1.05/1.26  thf('41', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.05/1.26            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['35', '40'])).
% 1.05/1.26  thf('42', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.05/1.26              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.05/1.26      inference('simplify', [status(thm)], ['41'])).
% 1.05/1.26  thf('43', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['9', '10'])).
% 1.05/1.26  thf('44', plain,
% 1.05/1.26      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.05/1.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.05/1.26  thf('45', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.05/1.26      inference('sup+', [status(thm)], ['43', '44'])).
% 1.05/1.26  thf('46', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.05/1.26           (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['42', '45'])).
% 1.05/1.26  thf('47', plain,
% 1.05/1.26      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.05/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.05/1.26      inference('sup+', [status(thm)], ['34', '46'])).
% 1.05/1.26  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('49', plain,
% 1.05/1.26      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.05/1.26      inference('demod', [status(thm)], ['47', '48'])).
% 1.05/1.26  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 1.05/1.26  
% 1.05/1.26  % SZS output end Refutation
% 1.05/1.26  
% 1.05/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
