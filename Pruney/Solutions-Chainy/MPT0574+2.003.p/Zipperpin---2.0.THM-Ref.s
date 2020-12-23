%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hoSIMgPQ5R

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:16 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 ( 668 expanded)
%              Number of equality atoms :   48 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','31','32','35'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_xboole_0 @ X40 @ X41 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hoSIMgPQ5R
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.79  % Solved by: fo/fo7.sh
% 0.61/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.79  % done 1164 iterations in 0.337s
% 0.61/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.79  % SZS output start Refutation
% 0.61/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.79  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.61/0.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.61/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.61/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.79  thf(d10_xboole_0, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.79  thf('0', plain,
% 0.61/0.79      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.61/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.79  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.61/0.79      inference('simplify', [status(thm)], ['0'])).
% 0.61/0.79  thf(t178_relat_1, conjecture,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ C ) =>
% 0.61/0.79       ( ( r1_tarski @ A @ B ) =>
% 0.61/0.79         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.79        ( ( v1_relat_1 @ C ) =>
% 0.61/0.79          ( ( r1_tarski @ A @ B ) =>
% 0.61/0.79            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.61/0.79    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.61/0.79  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(t28_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.61/0.79  thf('3', plain,
% 0.61/0.79      (![X12 : $i, X13 : $i]:
% 0.61/0.79         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.61/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.79  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.61/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.79  thf(t100_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.79  thf('5', plain,
% 0.61/0.79      (![X4 : $i, X5 : $i]:
% 0.61/0.79         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.79           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.79  thf('6', plain,
% 0.61/0.79      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.61/0.79      inference('sup+', [status(thm)], ['4', '5'])).
% 0.61/0.79  thf(t39_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.79  thf('7', plain,
% 0.61/0.79      (![X16 : $i, X17 : $i]:
% 0.61/0.79         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.61/0.79           = (k2_xboole_0 @ X16 @ X17))),
% 0.61/0.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.79  thf('8', plain,
% 0.61/0.79      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.61/0.79         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.61/0.79      inference('sup+', [status(thm)], ['6', '7'])).
% 0.61/0.79  thf(commutativity_k2_tarski, axiom,
% 0.61/0.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.61/0.79  thf('9', plain,
% 0.61/0.79      (![X27 : $i, X28 : $i]:
% 0.61/0.79         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.61/0.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.61/0.79  thf(l51_zfmisc_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.79  thf('10', plain,
% 0.61/0.79      (![X31 : $i, X32 : $i]:
% 0.61/0.79         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.61/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.79  thf('11', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.79      inference('sup+', [status(thm)], ['9', '10'])).
% 0.61/0.79  thf('12', plain,
% 0.61/0.79      (![X31 : $i, X32 : $i]:
% 0.61/0.79         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.61/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.79  thf('13', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.79      inference('sup+', [status(thm)], ['11', '12'])).
% 0.61/0.79  thf('14', plain,
% 0.61/0.79      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.61/0.79         = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.79      inference('demod', [status(thm)], ['8', '13'])).
% 0.61/0.79  thf(t3_boole, axiom,
% 0.61/0.79    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.79  thf('15', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.61/0.79      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.79  thf(t48_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.79  thf('16', plain,
% 0.61/0.79      (![X20 : $i, X21 : $i]:
% 0.61/0.79         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.61/0.79           = (k3_xboole_0 @ X20 @ X21))),
% 0.61/0.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.79  thf('17', plain,
% 0.61/0.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.79      inference('sup+', [status(thm)], ['15', '16'])).
% 0.61/0.79  thf(idempotence_k3_xboole_0, axiom,
% 0.61/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.79  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.61/0.79      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.79  thf('19', plain,
% 0.61/0.79      (![X4 : $i, X5 : $i]:
% 0.61/0.79         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.79           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.79  thf('20', plain,
% 0.61/0.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.79  thf('21', plain,
% 0.61/0.79      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.79      inference('demod', [status(thm)], ['17', '20'])).
% 0.61/0.79  thf('22', plain,
% 0.61/0.79      (![X27 : $i, X28 : $i]:
% 0.61/0.79         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.61/0.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.61/0.79  thf(t12_setfam_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.79  thf('23', plain,
% 0.61/0.79      (![X33 : $i, X34 : $i]:
% 0.61/0.79         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.61/0.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.61/0.79  thf('24', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.79      inference('sup+', [status(thm)], ['22', '23'])).
% 0.61/0.79  thf('25', plain,
% 0.61/0.79      (![X33 : $i, X34 : $i]:
% 0.61/0.79         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.61/0.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.61/0.79  thf('26', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.79      inference('sup+', [status(thm)], ['24', '25'])).
% 0.61/0.79  thf('27', plain,
% 0.61/0.79      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.79      inference('sup+', [status(thm)], ['21', '26'])).
% 0.61/0.79  thf(t17_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.79  thf('28', plain,
% 0.61/0.79      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.61/0.79      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.79  thf(t3_xboole_1, axiom,
% 0.61/0.79    (![A:$i]:
% 0.61/0.79     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.79  thf('29', plain,
% 0.61/0.79      (![X19 : $i]:
% 0.61/0.79         (((X19) = (k1_xboole_0)) | ~ (r1_tarski @ X19 @ k1_xboole_0))),
% 0.61/0.79      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.61/0.79  thf('30', plain,
% 0.61/0.79      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.61/0.79  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.79      inference('demod', [status(thm)], ['27', '30'])).
% 0.61/0.79  thf('32', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.79      inference('sup+', [status(thm)], ['11', '12'])).
% 0.61/0.79  thf('33', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.79      inference('sup+', [status(thm)], ['11', '12'])).
% 0.61/0.79  thf(t1_boole, axiom,
% 0.61/0.79    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.79  thf('34', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.61/0.79      inference('cnf', [status(esa)], [t1_boole])).
% 0.61/0.79  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.79      inference('sup+', [status(thm)], ['33', '34'])).
% 0.61/0.79  thf('36', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.79      inference('demod', [status(thm)], ['14', '31', '32', '35'])).
% 0.61/0.79  thf(t175_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ C ) =>
% 0.61/0.79       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.61/0.79         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.79  thf('37', plain,
% 0.61/0.79      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.61/0.79         (((k10_relat_1 @ X39 @ (k2_xboole_0 @ X40 @ X41))
% 0.61/0.79            = (k2_xboole_0 @ (k10_relat_1 @ X39 @ X40) @ 
% 0.61/0.79               (k10_relat_1 @ X39 @ X41)))
% 0.61/0.79          | ~ (v1_relat_1 @ X39))),
% 0.61/0.79      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.61/0.79  thf(t7_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.79  thf('38', plain,
% 0.61/0.79      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.61/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.79  thf(t1_xboole_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.61/0.79       ( r1_tarski @ A @ C ) ))).
% 0.61/0.79  thf('39', plain,
% 0.61/0.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.79         (~ (r1_tarski @ X9 @ X10)
% 0.61/0.79          | ~ (r1_tarski @ X10 @ X11)
% 0.61/0.79          | (r1_tarski @ X9 @ X11))),
% 0.61/0.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.61/0.79  thf('40', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.79         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.61/0.79      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.79  thf('41', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.79         (~ (r1_tarski @ (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.61/0.79          | ~ (v1_relat_1 @ X2)
% 0.61/0.79          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ X3))),
% 0.61/0.79      inference('sup-', [status(thm)], ['37', '40'])).
% 0.61/0.79  thf('42', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         (~ (r1_tarski @ (k10_relat_1 @ X1 @ sk_B) @ X0)
% 0.61/0.79          | (r1_tarski @ (k10_relat_1 @ X1 @ sk_A) @ X0)
% 0.61/0.79          | ~ (v1_relat_1 @ X1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['36', '41'])).
% 0.61/0.79  thf('43', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ X0)
% 0.61/0.79          | (r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B)))),
% 0.61/0.79      inference('sup-', [status(thm)], ['1', '42'])).
% 0.61/0.79  thf('44', plain,
% 0.61/0.79      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf('45', plain, (~ (v1_relat_1 @ sk_C)),
% 0.61/0.79      inference('sup-', [status(thm)], ['43', '44'])).
% 0.61/0.79  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf('47', plain, ($false), inference('demod', [status(thm)], ['45', '46'])).
% 0.61/0.79  
% 0.61/0.79  % SZS output end Refutation
% 0.61/0.79  
% 0.61/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
