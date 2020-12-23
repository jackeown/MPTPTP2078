%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmiVC3HFg3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:33 EST 2020

% Result     : Theorem 5.71s
% Output     : Refutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   68 (  86 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  611 ( 795 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) @ X15 )
        = ( k9_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','33'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmiVC3HFg3
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.71/5.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.71/5.90  % Solved by: fo/fo7.sh
% 5.71/5.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.71/5.90  % done 2523 iterations in 5.440s
% 5.71/5.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.71/5.90  % SZS output start Refutation
% 5.71/5.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.71/5.90  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.71/5.90  thf(sk_A_type, type, sk_A: $i).
% 5.71/5.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.71/5.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.71/5.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.71/5.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.71/5.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.71/5.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.71/5.90  thf(sk_C_type, type, sk_C: $i).
% 5.71/5.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.71/5.90  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.71/5.90  thf(sk_B_type, type, sk_B: $i).
% 5.71/5.90  thf(commutativity_k2_tarski, axiom,
% 5.71/5.90    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.71/5.90  thf('0', plain,
% 5.71/5.90      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 5.71/5.90      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.71/5.90  thf(t12_setfam_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]:
% 5.71/5.90     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.71/5.90  thf('1', plain,
% 5.71/5.90      (![X9 : $i, X10 : $i]:
% 5.71/5.90         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 5.71/5.90      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.71/5.90  thf('2', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i]:
% 5.71/5.90         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.71/5.90      inference('sup+', [status(thm)], ['0', '1'])).
% 5.71/5.90  thf('3', plain,
% 5.71/5.90      (![X9 : $i, X10 : $i]:
% 5.71/5.90         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 5.71/5.90      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.71/5.90  thf('4', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.71/5.90      inference('sup+', [status(thm)], ['2', '3'])).
% 5.71/5.90  thf(t17_xboole_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.71/5.90  thf('5', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 5.71/5.90      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.71/5.90  thf(t162_relat_1, axiom,
% 5.71/5.90    (![A:$i]:
% 5.71/5.90     ( ( v1_relat_1 @ A ) =>
% 5.71/5.90       ( ![B:$i,C:$i]:
% 5.71/5.90         ( ( r1_tarski @ B @ C ) =>
% 5.71/5.90           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 5.71/5.90             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 5.71/5.90  thf('6', plain,
% 5.71/5.90      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.71/5.90         (~ (r1_tarski @ X15 @ X16)
% 5.71/5.90          | ((k9_relat_1 @ (k7_relat_1 @ X17 @ X16) @ X15)
% 5.71/5.90              = (k9_relat_1 @ X17 @ X15))
% 5.71/5.90          | ~ (v1_relat_1 @ X17))),
% 5.71/5.90      inference('cnf', [status(esa)], [t162_relat_1])).
% 5.71/5.90  thf('7', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X2)
% 5.71/5.90          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 5.71/5.90              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 5.71/5.90      inference('sup-', [status(thm)], ['5', '6'])).
% 5.71/5.90  thf(fc8_funct_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]:
% 5.71/5.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.71/5.90       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 5.71/5.90         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 5.71/5.90  thf('8', plain,
% 5.71/5.90      (![X20 : $i, X21 : $i]:
% 5.71/5.90         (~ (v1_funct_1 @ X20)
% 5.71/5.90          | ~ (v1_relat_1 @ X20)
% 5.71/5.90          | (v1_funct_1 @ (k7_relat_1 @ X20 @ X21)))),
% 5.71/5.90      inference('cnf', [status(esa)], [fc8_funct_1])).
% 5.71/5.90  thf(dt_k7_relat_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]:
% 5.71/5.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 5.71/5.90  thf('9', plain,
% 5.71/5.90      (![X11 : $i, X12 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 5.71/5.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.71/5.90  thf(t139_funct_1, axiom,
% 5.71/5.90    (![A:$i,B:$i,C:$i]:
% 5.71/5.90     ( ( v1_relat_1 @ C ) =>
% 5.71/5.90       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 5.71/5.90         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.71/5.90  thf('10', plain,
% 5.71/5.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.71/5.90         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 5.71/5.90            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 5.71/5.90          | ~ (v1_relat_1 @ X23))),
% 5.71/5.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 5.71/5.90  thf(t145_funct_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]:
% 5.71/5.90     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.71/5.90       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 5.71/5.90  thf('11', plain,
% 5.71/5.90      (![X25 : $i, X26 : $i]:
% 5.71/5.90         ((r1_tarski @ (k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X26)) @ X26)
% 5.71/5.90          | ~ (v1_funct_1 @ X25)
% 5.71/5.90          | ~ (v1_relat_1 @ X25))),
% 5.71/5.90      inference('cnf', [status(esa)], [t145_funct_1])).
% 5.71/5.90  thf('12', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ 
% 5.71/5.90           (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 5.71/5.90            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 5.71/5.90           X0)
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 5.71/5.90          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 5.71/5.90      inference('sup+', [status(thm)], ['10', '11'])).
% 5.71/5.90  thf('13', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | (r1_tarski @ 
% 5.71/5.90             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 5.71/5.90              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 5.71/5.90             X2))),
% 5.71/5.90      inference('sup-', [status(thm)], ['9', '12'])).
% 5.71/5.90  thf('14', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ 
% 5.71/5.90           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 5.71/5.90            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 5.71/5.90           X2)
% 5.71/5.90          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 5.71/5.90          | ~ (v1_relat_1 @ X1))),
% 5.71/5.90      inference('simplify', [status(thm)], ['13'])).
% 5.71/5.90  thf('15', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_funct_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | (r1_tarski @ 
% 5.71/5.90             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 5.71/5.90              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 5.71/5.90             X2))),
% 5.71/5.90      inference('sup-', [status(thm)], ['8', '14'])).
% 5.71/5.90  thf('16', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ 
% 5.71/5.90           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 5.71/5.90            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 5.71/5.90           X2)
% 5.71/5.90          | ~ (v1_funct_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ X1))),
% 5.71/5.90      inference('simplify', [status(thm)], ['15'])).
% 5.71/5.90  thf('17', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ 
% 5.71/5.90           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 5.71/5.90           X0)
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_funct_1 @ X1))),
% 5.71/5.90      inference('sup+', [status(thm)], ['7', '16'])).
% 5.71/5.90  thf('18', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_funct_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | (r1_tarski @ 
% 5.71/5.90             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 5.71/5.90             X0))),
% 5.71/5.90      inference('simplify', [status(thm)], ['17'])).
% 5.71/5.90  thf('19', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X2)
% 5.71/5.90          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 5.71/5.90              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 5.71/5.90      inference('sup-', [status(thm)], ['5', '6'])).
% 5.71/5.90  thf(t148_relat_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]:
% 5.71/5.90     ( ( v1_relat_1 @ B ) =>
% 5.71/5.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 5.71/5.90  thf('20', plain,
% 5.71/5.90      (![X13 : $i, X14 : $i]:
% 5.71/5.90         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 5.71/5.90          | ~ (v1_relat_1 @ X13))),
% 5.71/5.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.71/5.90  thf('21', plain,
% 5.71/5.90      (![X13 : $i, X14 : $i]:
% 5.71/5.90         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 5.71/5.90          | ~ (v1_relat_1 @ X13))),
% 5.71/5.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.71/5.90  thf(t99_relat_1, axiom,
% 5.71/5.90    (![A:$i,B:$i]:
% 5.71/5.90     ( ( v1_relat_1 @ B ) =>
% 5.71/5.90       ( r1_tarski @
% 5.71/5.90         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 5.71/5.90  thf('22', plain,
% 5.71/5.90      (![X18 : $i, X19 : $i]:
% 5.71/5.90         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ 
% 5.71/5.90           (k2_relat_1 @ X18))
% 5.71/5.90          | ~ (v1_relat_1 @ X18))),
% 5.71/5.90      inference('cnf', [status(esa)], [t99_relat_1])).
% 5.71/5.90  thf('23', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i]:
% 5.71/5.90         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ X1))),
% 5.71/5.90      inference('sup+', [status(thm)], ['21', '22'])).
% 5.71/5.90  thf('24', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X1)
% 5.71/5.90          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 5.71/5.90      inference('simplify', [status(thm)], ['23'])).
% 5.71/5.90  thf('25', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 5.71/5.90           (k9_relat_1 @ X1 @ X0))
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.71/5.90      inference('sup+', [status(thm)], ['20', '24'])).
% 5.71/5.90  thf('26', plain,
% 5.71/5.90      (![X11 : $i, X12 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 5.71/5.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.71/5.90  thf('27', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X1)
% 5.71/5.90          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 5.71/5.90             (k9_relat_1 @ X1 @ X0)))),
% 5.71/5.90      inference('clc', [status(thm)], ['25', '26'])).
% 5.71/5.90  thf('28', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.71/5.90           (k9_relat_1 @ X2 @ X1))
% 5.71/5.90          | ~ (v1_relat_1 @ X2)
% 5.71/5.90          | ~ (v1_relat_1 @ X2))),
% 5.71/5.90      inference('sup+', [status(thm)], ['19', '27'])).
% 5.71/5.90  thf('29', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X2)
% 5.71/5.90          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.71/5.90             (k9_relat_1 @ X2 @ X1)))),
% 5.71/5.90      inference('simplify', [status(thm)], ['28'])).
% 5.71/5.90  thf(t19_xboole_1, axiom,
% 5.71/5.90    (![A:$i,B:$i,C:$i]:
% 5.71/5.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 5.71/5.90       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.71/5.90  thf('30', plain,
% 5.71/5.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.90         (~ (r1_tarski @ X2 @ X3)
% 5.71/5.90          | ~ (r1_tarski @ X2 @ X4)
% 5.71/5.90          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 5.71/5.90      inference('cnf', [status(esa)], [t19_xboole_1])).
% 5.71/5.90  thf('31', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X1)
% 5.71/5.90          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 5.71/5.90             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 5.71/5.90          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 5.71/5.90      inference('sup-', [status(thm)], ['29', '30'])).
% 5.71/5.90  thf('32', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         (~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_funct_1 @ X1)
% 5.71/5.90          | (r1_tarski @ 
% 5.71/5.90             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 5.71/5.90             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 5.71/5.90          | ~ (v1_relat_1 @ X1))),
% 5.71/5.90      inference('sup-', [status(thm)], ['18', '31'])).
% 5.71/5.90  thf('33', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ 
% 5.71/5.90           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 5.71/5.90           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 5.71/5.90          | ~ (v1_funct_1 @ X1)
% 5.71/5.90          | ~ (v1_relat_1 @ X1))),
% 5.71/5.90      inference('simplify', [status(thm)], ['32'])).
% 5.71/5.90  thf('34', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.90         ((r1_tarski @ 
% 5.71/5.90           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 5.71/5.90           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 5.71/5.90          | ~ (v1_relat_1 @ X1)
% 5.71/5.90          | ~ (v1_funct_1 @ X1))),
% 5.71/5.90      inference('sup+', [status(thm)], ['4', '33'])).
% 5.71/5.90  thf(t149_funct_1, conjecture,
% 5.71/5.90    (![A:$i,B:$i,C:$i]:
% 5.71/5.90     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.71/5.90       ( r1_tarski @
% 5.71/5.90         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 5.71/5.90         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 5.71/5.90  thf(zf_stmt_0, negated_conjecture,
% 5.71/5.90    (~( ![A:$i,B:$i,C:$i]:
% 5.71/5.90        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.71/5.90          ( r1_tarski @
% 5.71/5.90            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 5.71/5.90            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 5.71/5.90    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 5.71/5.90  thf('35', plain,
% 5.71/5.90      (~ (r1_tarski @ 
% 5.71/5.90          (k9_relat_1 @ sk_C @ 
% 5.71/5.90           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 5.71/5.90          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 5.71/5.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.71/5.90  thf('36', plain,
% 5.71/5.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.71/5.90      inference('sup+', [status(thm)], ['2', '3'])).
% 5.71/5.90  thf('37', plain,
% 5.71/5.90      (~ (r1_tarski @ 
% 5.71/5.90          (k9_relat_1 @ sk_C @ 
% 5.71/5.90           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 5.71/5.90          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 5.71/5.90      inference('demod', [status(thm)], ['35', '36'])).
% 5.71/5.90  thf('38', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 5.71/5.90      inference('sup-', [status(thm)], ['34', '37'])).
% 5.71/5.90  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 5.71/5.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.71/5.90  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 5.71/5.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.71/5.90  thf('41', plain, ($false),
% 5.71/5.90      inference('demod', [status(thm)], ['38', '39', '40'])).
% 5.71/5.90  
% 5.71/5.90  % SZS output end Refutation
% 5.71/5.90  
% 5.71/5.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
