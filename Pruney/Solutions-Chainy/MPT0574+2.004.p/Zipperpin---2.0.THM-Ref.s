%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gunoa03fOx

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (  90 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  475 ( 578 expanded)
%              Number of equality atoms :   45 (  51 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','34','39'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X27 @ X28 ) @ ( k10_relat_1 @ X27 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gunoa03fOx
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 304 iterations in 0.095s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(t178_relat_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.54         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( v1_relat_1 @ C ) =>
% 0.20/0.54          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.54            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.20/0.54  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('2', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.54  thf(t19_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.20/0.54       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X6 @ X7)
% 0.20/0.54          | ~ (r1_tarski @ X6 @ X8)
% 0.20/0.54          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('5', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.54  thf(t17_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.20/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.54          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.54  thf(t48_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.20/0.54           = (k3_xboole_0 @ X17 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.54  thf(t38_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.54       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (((X11) = (k1_xboole_0))
% 0.20/0.54          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.54          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.54        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.54  thf(t36_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf(t39_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.20/0.54           = (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf(t3_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('18', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.20/0.54           = (k3_xboole_0 @ X17 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf(commutativity_k2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i]:
% 0.20/0.54         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.54  thf(t12_setfam_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.20/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.54  thf(t3_xboole_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X16 : $i]:
% 0.20/0.54         (((X16) = (k1_xboole_0)) | ~ (r1_tarski @ X16 @ k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.54  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.20/0.54           = (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.54  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.54  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i]:
% 0.20/0.54         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.54  thf(l51_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['17', '34', '39'])).
% 0.20/0.54  thf(t175_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.54         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.54         (((k10_relat_1 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 0.20/0.54            = (k2_xboole_0 @ (k10_relat_1 @ X27 @ X28) @ 
% 0.20/0.54               (k10_relat_1 @ X27 @ X29)))
% 0.20/0.54          | ~ (v1_relat_1 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.20/0.54  thf(t7_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.20/0.54           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ X2))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain, (~ (v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.54  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
