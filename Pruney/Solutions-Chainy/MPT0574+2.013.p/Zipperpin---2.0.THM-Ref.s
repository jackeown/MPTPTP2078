%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dWMroTaTqn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:18 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 121 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  515 ( 786 expanded)
%              Number of equality atoms :   56 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','41','42','45'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_xboole_0 @ X33 @ X34 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dWMroTaTqn
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 647 iterations in 0.142s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(t178_relat_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ C ) =>
% 0.37/0.59       ( ( r1_tarski @ A @ B ) =>
% 0.37/0.59         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.59        ( ( v1_relat_1 @ C ) =>
% 0.37/0.59          ( ( r1_tarski @ A @ B ) =>
% 0.37/0.59            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.37/0.59  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t28_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.59  thf('2', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.59  thf(t100_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X1 : $i, X2 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.59           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.37/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.59  thf(t39_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.37/0.59           = (k2_xboole_0 @ X10 @ X11))),
% 0.37/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.37/0.59         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.59  thf(commutativity_k2_tarski, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X24 : $i, X25 : $i]:
% 0.37/0.59         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.59  thf(l51_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X28 : $i, X29 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.37/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (![X28 : $i, X29 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.37/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.37/0.59         = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['6', '11'])).
% 0.37/0.60  thf(t17_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.37/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.60  thf(t3_xboole_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X13 : $i]:
% 0.37/0.60         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.60           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.60  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf(t3_boole, axiom,
% 0.37/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.60  thf('21', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.37/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['17', '22'])).
% 0.37/0.60  thf('24', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(t85_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X21 @ X22)
% 0.37/0.60          | (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.60  thf(t83_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X18 : $i, X19 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.37/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.60  thf(t48_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ sk_A @ sk_A)
% 0.37/0.60           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ sk_A @ sk_A)
% 0.37/0.60           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 0.37/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      (((k5_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['23', '32'])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X24 : $i, X25 : $i]:
% 0.37/0.60         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.60  thf(t12_setfam_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X30 : $i, X31 : $i]:
% 0.37/0.60         ((k1_setfam_1 @ (k2_tarski @ X30 @ X31)) = (k3_xboole_0 @ X30 @ X31))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (![X30 : $i, X31 : $i]:
% 0.37/0.60         ((k1_setfam_1 @ (k2_tarski @ X30 @ X31)) = (k3_xboole_0 @ X30 @ X31))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.60  thf('41', plain, (((k5_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['33', '40'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.60  thf(t1_boole, axiom,
% 0.37/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.60  thf('44', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.37/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.60  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.60  thf('46', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.60      inference('demod', [status(thm)], ['12', '41', '42', '45'])).
% 0.37/0.60  thf(t175_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ C ) =>
% 0.37/0.60       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.37/0.60         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.60         (((k10_relat_1 @ X32 @ (k2_xboole_0 @ X33 @ X34))
% 0.37/0.60            = (k2_xboole_0 @ (k10_relat_1 @ X32 @ X33) @ 
% 0.37/0.60               (k10_relat_1 @ X32 @ X34)))
% 0.37/0.60          | ~ (v1_relat_1 @ X32))),
% 0.37/0.60      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.37/0.60  thf(t7_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('48', plain,
% 0.37/0.60      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.37/0.60           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.37/0.60          | ~ (v1_relat_1 @ X2))),
% 0.37/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.60  thf('50', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['46', '49'])).
% 0.37/0.60  thf('51', plain,
% 0.37/0.60      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('52', plain, (~ (v1_relat_1 @ sk_C)),
% 0.37/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.60  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
