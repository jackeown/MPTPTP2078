%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Ry4QBqJ1c

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:18 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 119 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  440 ( 779 expanded)
%              Number of equality atoms :   49 (  88 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
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

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('38',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','35','36','37'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Ry4QBqJ1c
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 468 iterations in 0.149s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(t178_relat_1, conjecture,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ C ) =>
% 0.42/0.61       ( ( r1_tarski @ A @ B ) =>
% 0.42/0.61         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.61        ( ( v1_relat_1 @ C ) =>
% 0.42/0.61          ( ( r1_tarski @ A @ B ) =>
% 0.42/0.61            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.42/0.61  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t28_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('2', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.61  thf(t100_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X1 : $i, X2 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.42/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf(t39_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.42/0.61           = (k2_xboole_0 @ X8 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.42/0.61         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.42/0.61  thf(commutativity_k2_tarski, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.42/0.61  thf(l51_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.42/0.61         = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['6', '11'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf(t1_boole, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.61  thf('14', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.42/0.61  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.42/0.61           = (k2_xboole_0 @ X8 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.42/0.61  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.42/0.61  thf(t48_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X11 : $i, X12 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.42/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.42/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.42/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.61  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X1 : $i, X2 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.42/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['21', '24'])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.42/0.61  thf(t12_setfam_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.42/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.42/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf(t17_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.42/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.61  thf(t3_xboole_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X10 : $i]:
% 0.42/0.61         (((X10) = (k1_xboole_0)) | ~ (r1_tarski @ X10 @ k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['30', '33'])).
% 0.42/0.61  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['25', '34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf('38', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['12', '35', '36', '37'])).
% 0.42/0.61  thf(t175_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ C ) =>
% 0.42/0.61       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.42/0.61         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.61         (((k10_relat_1 @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 0.42/0.61            = (k2_xboole_0 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.42/0.61               (k10_relat_1 @ X24 @ X26)))
% 0.42/0.61          | ~ (v1_relat_1 @ X24))),
% 0.42/0.61      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.42/0.61  thf(t7_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.42/0.61           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X2))),
% 0.42/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['38', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('44', plain, (~ (v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.46/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
