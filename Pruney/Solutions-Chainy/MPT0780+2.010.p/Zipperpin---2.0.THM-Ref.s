%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Ntx0St6SJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:26 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 101 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  604 ( 819 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k8_relat_1 @ X13 @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X22 @ X24 ) @ X23 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X22 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_wellord1 @ X19 @ X18 )
        = ( k8_relat_1 @ X18 @ ( k7_relat_1 @ X19 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Ntx0St6SJ
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:29:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.76/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/1.01  % Solved by: fo/fo7.sh
% 0.76/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.01  % done 753 iterations in 0.565s
% 0.76/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/1.01  % SZS output start Refutation
% 0.76/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/1.01  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.76/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.01  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.76/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/1.01  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.76/1.01  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.76/1.01  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.76/1.01  thf(t29_wellord1, conjecture,
% 0.76/1.01    (![A:$i,B:$i,C:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ C ) =>
% 0.76/1.01       ( ( r1_tarski @ A @ B ) =>
% 0.76/1.01         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.76/1.01           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.76/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.76/1.01        ( ( v1_relat_1 @ C ) =>
% 0.76/1.01          ( ( r1_tarski @ A @ B ) =>
% 0.76/1.01            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.76/1.01              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.76/1.01    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.76/1.01  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf(t20_wellord1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ B ) =>
% 0.76/1.01       ( ( r1_tarski @
% 0.76/1.01           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.76/1.01         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.76/1.01  thf('1', plain,
% 0.76/1.01      (![X20 : $i, X21 : $i]:
% 0.76/1.01         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X20 @ X21)) @ X21)
% 0.76/1.01          | ~ (v1_relat_1 @ X20))),
% 0.76/1.01      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.76/1.01  thf(d6_relat_1, axiom,
% 0.76/1.01    (![A:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ A ) =>
% 0.76/1.01       ( ( k3_relat_1 @ A ) =
% 0.76/1.01         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.76/1.01  thf('2', plain,
% 0.76/1.01      (![X11 : $i]:
% 0.76/1.01         (((k3_relat_1 @ X11)
% 0.76/1.01            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.76/1.01          | ~ (v1_relat_1 @ X11))),
% 0.76/1.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.76/1.01  thf(commutativity_k2_tarski, axiom,
% 0.76/1.01    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.76/1.01  thf('3', plain,
% 0.76/1.01      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.76/1.01      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/1.01  thf(l51_zfmisc_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/1.01  thf('4', plain,
% 0.76/1.01      (![X9 : $i, X10 : $i]:
% 0.76/1.01         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.76/1.01      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.76/1.01  thf('5', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('sup+', [status(thm)], ['3', '4'])).
% 0.76/1.01  thf('6', plain,
% 0.76/1.01      (![X9 : $i, X10 : $i]:
% 0.76/1.01         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.76/1.01      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.76/1.01  thf('7', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('sup+', [status(thm)], ['5', '6'])).
% 0.76/1.01  thf(t7_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.76/1.01  thf('8', plain,
% 0.76/1.01      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.76/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/1.01  thf(t1_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i]:
% 0.76/1.01     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.76/1.01       ( r1_tarski @ A @ C ) ))).
% 0.76/1.01  thf('9', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (r1_tarski @ X0 @ X1)
% 0.76/1.01          | ~ (r1_tarski @ X1 @ X2)
% 0.76/1.01          | (r1_tarski @ X0 @ X2))),
% 0.76/1.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/1.01  thf('10', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.76/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/1.01  thf('11', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.76/1.01      inference('sup-', [status(thm)], ['7', '10'])).
% 0.76/1.01  thf('12', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.76/1.01          | ~ (v1_relat_1 @ X0)
% 0.76/1.01          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['2', '11'])).
% 0.76/1.01  thf('13', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X1)
% 0.76/1.01          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['1', '12'])).
% 0.76/1.01  thf(dt_k2_wellord1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.76/1.01  thf('14', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k2_wellord1 @ X16 @ X17)))),
% 0.76/1.01      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/1.01  thf('15', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ X1))),
% 0.76/1.01      inference('clc', [status(thm)], ['13', '14'])).
% 0.76/1.01  thf('16', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (r1_tarski @ X0 @ X1)
% 0.76/1.01          | ~ (r1_tarski @ X1 @ X2)
% 0.76/1.01          | (r1_tarski @ X0 @ X2))),
% 0.76/1.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/1.01  thf('17', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X1)
% 0.76/1.01          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.76/1.01          | ~ (r1_tarski @ X0 @ X2))),
% 0.76/1.01      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/1.01  thf('18', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.76/1.01          | ~ (v1_relat_1 @ X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['0', '17'])).
% 0.76/1.01  thf(t125_relat_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ B ) =>
% 0.76/1.01       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.76/1.01         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.76/1.01  thf('19', plain,
% 0.76/1.01      (![X12 : $i, X13 : $i]:
% 0.76/1.01         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.76/1.01          | ((k8_relat_1 @ X13 @ X12) = (X12))
% 0.76/1.01          | ~ (v1_relat_1 @ X12))),
% 0.76/1.01      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.76/1.01  thf('20', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/1.01          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/1.01              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/1.01  thf('21', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k2_wellord1 @ X16 @ X17)))),
% 0.76/1.01      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/1.01  thf('22', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/1.01            = (k2_wellord1 @ X0 @ sk_A))
% 0.76/1.01          | ~ (v1_relat_1 @ X0))),
% 0.76/1.01      inference('clc', [status(thm)], ['20', '21'])).
% 0.76/1.01  thf(t27_wellord1, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ C ) =>
% 0.76/1.01       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.76/1.01         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.76/1.01  thf('23', plain,
% 0.76/1.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/1.01         (((k2_wellord1 @ (k2_wellord1 @ X22 @ X24) @ X23)
% 0.76/1.01            = (k2_wellord1 @ (k2_wellord1 @ X22 @ X23) @ X24))
% 0.76/1.01          | ~ (v1_relat_1 @ X22))),
% 0.76/1.01      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.76/1.01  thf('24', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('25', plain,
% 0.76/1.01      (![X20 : $i, X21 : $i]:
% 0.76/1.01         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X20 @ X21)) @ X21)
% 0.76/1.01          | ~ (v1_relat_1 @ X20))),
% 0.76/1.01      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.76/1.01  thf('26', plain,
% 0.76/1.01      (![X11 : $i]:
% 0.76/1.01         (((k3_relat_1 @ X11)
% 0.76/1.01            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.76/1.01          | ~ (v1_relat_1 @ X11))),
% 0.76/1.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.76/1.01  thf('27', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.76/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/1.01  thf('28', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.76/1.01          | ~ (v1_relat_1 @ X0)
% 0.76/1.01          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/1.01  thf('29', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X1)
% 0.76/1.01          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['25', '28'])).
% 0.76/1.01  thf('30', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k2_wellord1 @ X16 @ X17)))),
% 0.76/1.01      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/1.01  thf('31', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ X1))),
% 0.76/1.01      inference('clc', [status(thm)], ['29', '30'])).
% 0.76/1.01  thf('32', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (r1_tarski @ X0 @ X1)
% 0.76/1.01          | ~ (r1_tarski @ X1 @ X2)
% 0.76/1.01          | (r1_tarski @ X0 @ X2))),
% 0.76/1.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/1.01  thf('33', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X1)
% 0.76/1.01          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.76/1.01          | ~ (r1_tarski @ X0 @ X2))),
% 0.76/1.01      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/1.01  thf('34', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.76/1.01          | ~ (v1_relat_1 @ X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['24', '33'])).
% 0.76/1.01  thf(t97_relat_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ B ) =>
% 0.76/1.01       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.76/1.01         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.76/1.01  thf('35', plain,
% 0.76/1.01      (![X14 : $i, X15 : $i]:
% 0.76/1.01         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.76/1.01          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 0.76/1.01          | ~ (v1_relat_1 @ X14))),
% 0.76/1.01      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.76/1.01  thf('36', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/1.01          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/1.01              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/1.01  thf('37', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k2_wellord1 @ X16 @ X17)))),
% 0.76/1.01      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/1.01  thf('38', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/1.01            = (k2_wellord1 @ X0 @ sk_A))
% 0.76/1.01          | ~ (v1_relat_1 @ X0))),
% 0.76/1.01      inference('clc', [status(thm)], ['36', '37'])).
% 0.76/1.01  thf(t18_wellord1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( v1_relat_1 @ B ) =>
% 0.76/1.01       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.76/1.01  thf('39', plain,
% 0.76/1.01      (![X18 : $i, X19 : $i]:
% 0.76/1.01         (((k2_wellord1 @ X19 @ X18)
% 0.76/1.01            = (k8_relat_1 @ X18 @ (k7_relat_1 @ X19 @ X18)))
% 0.76/1.01          | ~ (v1_relat_1 @ X19))),
% 0.76/1.01      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.76/1.01  thf('40', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/1.01            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 0.76/1.01          | ~ (v1_relat_1 @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/1.01      inference('sup+', [status(thm)], ['38', '39'])).
% 0.76/1.01  thf('41', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k2_wellord1 @ X16 @ X17)))),
% 0.76/1.01      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/1.01  thf('42', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X0)
% 0.76/1.01          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/1.01              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 0.76/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.76/1.01  thf('43', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.76/1.01            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 0.76/1.01          | ~ (v1_relat_1 @ X0)
% 0.76/1.01          | ~ (v1_relat_1 @ X0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['23', '42'])).
% 0.76/1.01  thf('44', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (~ (v1_relat_1 @ X0)
% 0.76/1.01          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.76/1.01              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 0.76/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.76/1.01  thf('45', plain,
% 0.76/1.01      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.76/1.01         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('46', plain,
% 0.76/1.01      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 0.76/1.01          != (k2_wellord1 @ sk_C @ sk_A))
% 0.76/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.76/1.01      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/1.01  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('48', plain,
% 0.76/1.01      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 0.76/1.01         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.76/1.01      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/1.01  thf('49', plain,
% 0.76/1.01      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 0.76/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.76/1.01      inference('sup-', [status(thm)], ['22', '48'])).
% 0.76/1.01  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('51', plain,
% 0.76/1.01      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.76/1.01      inference('demod', [status(thm)], ['49', '50'])).
% 0.76/1.01  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.76/1.01  
% 0.76/1.01  % SZS output end Refutation
% 0.76/1.01  
% 0.87/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
