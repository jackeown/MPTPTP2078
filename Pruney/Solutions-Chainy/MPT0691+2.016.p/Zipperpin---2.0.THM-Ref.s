%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mRlmSu3baV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:19 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 146 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  609 (1220 expanded)
%              Number of equality atoms :   40 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X20: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','38'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','44','45'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mRlmSu3baV
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.84/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.04  % Solved by: fo/fo7.sh
% 0.84/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.04  % done 1070 iterations in 0.593s
% 0.84/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.04  % SZS output start Refutation
% 0.84/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.04  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.84/1.04  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.84/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.04  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.84/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.04  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.84/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.04  thf(t146_funct_1, conjecture,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ B ) =>
% 0.84/1.04       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.84/1.04         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.84/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.04    (~( ![A:$i,B:$i]:
% 0.84/1.04        ( ( v1_relat_1 @ B ) =>
% 0.84/1.04          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.84/1.04            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.84/1.04    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.84/1.04  thf('0', plain,
% 0.84/1.04      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t148_relat_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ B ) =>
% 0.84/1.04       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.84/1.04  thf('1', plain,
% 0.84/1.04      (![X16 : $i, X17 : $i]:
% 0.84/1.04         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.84/1.04          | ~ (v1_relat_1 @ X16))),
% 0.84/1.04      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.84/1.04  thf(t169_relat_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ A ) =>
% 0.84/1.04       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.84/1.04  thf('2', plain,
% 0.84/1.04      (![X20 : $i]:
% 0.84/1.04         (((k10_relat_1 @ X20 @ (k2_relat_1 @ X20)) = (k1_relat_1 @ X20))
% 0.84/1.04          | ~ (v1_relat_1 @ X20))),
% 0.84/1.04      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.84/1.04  thf('3', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.84/1.04            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.84/1.04          | ~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['1', '2'])).
% 0.84/1.04  thf(dt_k7_relat_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.84/1.04  thf('4', plain,
% 0.84/1.04      (![X14 : $i, X15 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.84/1.04  thf('5', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X1)
% 0.84/1.04          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.84/1.04              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.84/1.04      inference('clc', [status(thm)], ['3', '4'])).
% 0.84/1.04  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t28_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.04  thf('7', plain,
% 0.84/1.04      (![X8 : $i, X9 : $i]:
% 0.84/1.04         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.84/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.04  thf('8', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.84/1.04      inference('sup-', [status(thm)], ['6', '7'])).
% 0.84/1.04  thf('9', plain,
% 0.84/1.04      (![X20 : $i]:
% 0.84/1.04         (((k10_relat_1 @ X20 @ (k2_relat_1 @ X20)) = (k1_relat_1 @ X20))
% 0.84/1.04          | ~ (v1_relat_1 @ X20))),
% 0.84/1.04      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.84/1.04  thf(t139_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ C ) =>
% 0.84/1.04       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.84/1.04         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.84/1.04  thf('10', plain,
% 0.84/1.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.04         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.84/1.04            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.84/1.04          | ~ (v1_relat_1 @ X24))),
% 0.84/1.04      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.84/1.04  thf(t167_relat_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ B ) =>
% 0.84/1.04       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.84/1.04  thf('11', plain,
% 0.84/1.04      (![X18 : $i, X19 : $i]:
% 0.84/1.04         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 0.84/1.04          | ~ (v1_relat_1 @ X18))),
% 0.84/1.04      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.84/1.04  thf('12', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.84/1.04           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 0.84/1.04          | ~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['10', '11'])).
% 0.84/1.04  thf('13', plain,
% 0.84/1.04      (![X14 : $i, X15 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.84/1.04  thf('14', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X1)
% 0.84/1.04          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.84/1.04             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 0.84/1.04      inference('clc', [status(thm)], ['12', '13'])).
% 0.84/1.04  thf('15', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.84/1.04           (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0))),
% 0.84/1.04      inference('sup+', [status(thm)], ['9', '14'])).
% 0.84/1.04  thf('16', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X0)
% 0.84/1.04          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.84/1.04             (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 0.84/1.04      inference('simplify', [status(thm)], ['15'])).
% 0.84/1.04  thf('17', plain,
% 0.84/1.04      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.84/1.04        | ~ (v1_relat_1 @ sk_B))),
% 0.84/1.04      inference('sup+', [status(thm)], ['8', '16'])).
% 0.84/1.04  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('19', plain,
% 0.84/1.04      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.84/1.04      inference('demod', [status(thm)], ['17', '18'])).
% 0.84/1.04  thf(t87_relat_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ B ) =>
% 0.84/1.04       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.84/1.04  thf('20', plain,
% 0.84/1.04      (![X21 : $i, X22 : $i]:
% 0.84/1.04         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X22)) @ X22)
% 0.84/1.04          | ~ (v1_relat_1 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.84/1.04  thf(d10_xboole_0, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.04  thf('21', plain,
% 0.84/1.04      (![X0 : $i, X2 : $i]:
% 0.84/1.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.84/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.04  thf('22', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.84/1.04          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.04  thf('23', plain,
% 0.84/1.04      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.84/1.04        | ~ (v1_relat_1 @ sk_B))),
% 0.84/1.04      inference('sup-', [status(thm)], ['19', '22'])).
% 0.84/1.04  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('25', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.84/1.04      inference('demod', [status(thm)], ['23', '24'])).
% 0.84/1.04  thf('26', plain,
% 0.84/1.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.04         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.84/1.04            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.84/1.04          | ~ (v1_relat_1 @ X24))),
% 0.84/1.04      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.84/1.04  thf('27', plain,
% 0.84/1.04      (![X18 : $i, X19 : $i]:
% 0.84/1.04         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 0.84/1.04          | ~ (v1_relat_1 @ X18))),
% 0.84/1.04      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.84/1.04  thf('28', plain,
% 0.84/1.04      (![X8 : $i, X9 : $i]:
% 0.84/1.04         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.84/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.04  thf('29', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X0)
% 0.84/1.04          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.84/1.04              = (k10_relat_1 @ X0 @ X1)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['27', '28'])).
% 0.84/1.04  thf(commutativity_k2_tarski, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.84/1.04  thf('30', plain,
% 0.84/1.04      (![X10 : $i, X11 : $i]:
% 0.84/1.04         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.84/1.04      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.04  thf(t12_setfam_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.84/1.04  thf('31', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i]:
% 0.84/1.04         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.84/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.04  thf('32', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.04      inference('sup+', [status(thm)], ['30', '31'])).
% 0.84/1.04  thf('33', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i]:
% 0.84/1.04         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.84/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.04  thf('34', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.04      inference('sup+', [status(thm)], ['32', '33'])).
% 0.84/1.04  thf('35', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X0)
% 0.84/1.04          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.84/1.04              = (k10_relat_1 @ X0 @ X1)))),
% 0.84/1.04      inference('demod', [status(thm)], ['29', '34'])).
% 0.84/1.04  thf('36', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.84/1.04            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.84/1.04            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.84/1.04          | ~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['26', '35'])).
% 0.84/1.04  thf('37', plain,
% 0.84/1.04      (![X14 : $i, X15 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.84/1.04  thf('38', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X1)
% 0.84/1.05          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.84/1.05              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.84/1.05              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 0.84/1.05      inference('clc', [status(thm)], ['36', '37'])).
% 0.84/1.05  thf('39', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ sk_A @ 
% 0.84/1.05            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 0.84/1.05            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B))),
% 0.84/1.05      inference('sup+', [status(thm)], ['25', '38'])).
% 0.84/1.05  thf(t17_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.84/1.05      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      (![X8 : $i, X9 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.84/1.05      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.05  thf('42', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.84/1.05           = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.05  thf('43', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['32', '33'])).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.84/1.05           = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('demod', [status(thm)], ['42', '43'])).
% 0.84/1.05  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('46', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 0.84/1.05           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['39', '44', '45'])).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      ((((k3_xboole_0 @ sk_A @ 
% 0.84/1.05          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.84/1.05          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B))),
% 0.84/1.05      inference('sup+', [status(thm)], ['5', '46'])).
% 0.84/1.05  thf('48', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['23', '24'])).
% 0.84/1.05  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('50', plain,
% 0.84/1.05      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.84/1.05         = (sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['32', '33'])).
% 0.84/1.05  thf('52', plain,
% 0.84/1.05      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.84/1.05      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.84/1.05  thf('53', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.84/1.05      inference('sup+', [status(thm)], ['51', '52'])).
% 0.84/1.05  thf('54', plain,
% 0.84/1.05      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['50', '53'])).
% 0.84/1.05  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
