%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WVsBG0mLrc

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:39 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   68 (  76 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  439 ( 527 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t129_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X45 ) @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X52: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t118_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X43 @ X44 ) ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X52: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X45 ) @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('21',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( ( k8_relat_1 @ X50 @ X49 )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k8_relat_1 @ X48 @ X47 )
        = ( k5_relat_1 @ X47 @ ( k6_relat_1 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('25',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X53 @ ( k6_relat_1 @ X54 ) ) @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_relat_1 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['23','32'])).

thf('34',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WVsBG0mLrc
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.92  % Solved by: fo/fo7.sh
% 0.72/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.92  % done 876 iterations in 0.463s
% 0.72/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.92  % SZS output start Refutation
% 0.72/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.72/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.92  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.72/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.72/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.92  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.72/0.92  thf(commutativity_k2_tarski, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.72/0.92  thf('0', plain,
% 0.72/0.92      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.72/0.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.72/0.92  thf(t12_setfam_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.92  thf('1', plain,
% 0.72/0.92      (![X35 : $i, X36 : $i]:
% 0.72/0.92         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.72/0.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.72/0.92  thf('2', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.92      inference('sup+', [status(thm)], ['0', '1'])).
% 0.72/0.92  thf('3', plain,
% 0.72/0.92      (![X35 : $i, X36 : $i]:
% 0.72/0.92         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.72/0.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.72/0.92  thf('4', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.72/0.92  thf(t129_relat_1, conjecture,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ C ) =>
% 0.72/0.92       ( ( r1_tarski @ A @ B ) =>
% 0.72/0.92         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.72/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.92        ( ( v1_relat_1 @ C ) =>
% 0.72/0.92          ( ( r1_tarski @ A @ B ) =>
% 0.72/0.92            ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.72/0.92              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.72/0.92    inference('cnf.neg', [status(esa)], [t129_relat_1])).
% 0.72/0.92  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(t119_relat_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ B ) =>
% 0.72/0.92       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.72/0.92         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.72/0.92  thf('6', plain,
% 0.72/0.92      (![X45 : $i, X46 : $i]:
% 0.72/0.92         (((k2_relat_1 @ (k8_relat_1 @ X46 @ X45))
% 0.72/0.92            = (k3_xboole_0 @ (k2_relat_1 @ X45) @ X46))
% 0.72/0.92          | ~ (v1_relat_1 @ X45))),
% 0.72/0.92      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.72/0.92  thf(t71_relat_1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.72/0.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.72/0.92  thf('7', plain, (![X52 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X52)) = (X52))),
% 0.72/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.72/0.92  thf(t118_relat_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ B ) =>
% 0.72/0.92       ( r1_tarski @
% 0.72/0.92         ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.72/0.92  thf('8', plain,
% 0.72/0.92      (![X43 : $i, X44 : $i]:
% 0.72/0.92         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X43 @ X44)) @ 
% 0.72/0.92           (k2_relat_1 @ X44))
% 0.72/0.92          | ~ (v1_relat_1 @ X44))),
% 0.72/0.92      inference('cnf', [status(esa)], [t118_relat_1])).
% 0.72/0.92  thf('9', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.72/0.92           X0)
% 0.72/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.72/0.92      inference('sup+', [status(thm)], ['7', '8'])).
% 0.72/0.92  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.72/0.92  thf('10', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 0.72/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.72/0.92  thf('11', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.72/0.92      inference('demod', [status(thm)], ['9', '10'])).
% 0.72/0.92  thf('12', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.72/0.92           X1)
% 0.72/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.72/0.92      inference('sup+', [status(thm)], ['6', '11'])).
% 0.72/0.92  thf('13', plain, (![X52 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X52)) = (X52))),
% 0.72/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.72/0.92  thf('14', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 0.72/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.72/0.92  thf('15', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.72/0.92      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.72/0.92  thf(t1_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.72/0.92       ( r1_tarski @ A @ C ) ))).
% 0.72/0.92  thf('16', plain,
% 0.72/0.92      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.72/0.92         (~ (r1_tarski @ X3 @ X4)
% 0.72/0.92          | ~ (r1_tarski @ X4 @ X5)
% 0.72/0.92          | (r1_tarski @ X3 @ X5))),
% 0.72/0.92      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.72/0.92  thf('17', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.72/0.92      inference('sup-', [status(thm)], ['15', '16'])).
% 0.72/0.92  thf('18', plain,
% 0.72/0.92      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.72/0.92      inference('sup-', [status(thm)], ['5', '17'])).
% 0.72/0.92  thf('19', plain,
% 0.72/0.92      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.72/0.92      inference('sup+', [status(thm)], ['4', '18'])).
% 0.72/0.92  thf('20', plain,
% 0.72/0.92      (![X45 : $i, X46 : $i]:
% 0.72/0.92         (((k2_relat_1 @ (k8_relat_1 @ X46 @ X45))
% 0.72/0.92            = (k3_xboole_0 @ (k2_relat_1 @ X45) @ X46))
% 0.72/0.92          | ~ (v1_relat_1 @ X45))),
% 0.72/0.92      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.72/0.92  thf(t125_relat_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ B ) =>
% 0.72/0.92       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.72/0.92         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.72/0.92  thf('21', plain,
% 0.72/0.92      (![X49 : $i, X50 : $i]:
% 0.72/0.92         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 0.72/0.92          | ((k8_relat_1 @ X50 @ X49) = (X49))
% 0.72/0.92          | ~ (v1_relat_1 @ X49))),
% 0.72/0.92      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.72/0.92  thf('22', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2)
% 0.72/0.92          | ~ (v1_relat_1 @ X1)
% 0.72/0.92          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.72/0.92          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))
% 0.72/0.92              = (k8_relat_1 @ X0 @ X1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.92  thf('23', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.72/0.92            = (k8_relat_1 @ sk_A @ X0))
% 0.72/0.92          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.72/0.92          | ~ (v1_relat_1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['19', '22'])).
% 0.72/0.92  thf(t123_relat_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ B ) =>
% 0.72/0.92       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.72/0.92  thf('24', plain,
% 0.72/0.92      (![X47 : $i, X48 : $i]:
% 0.72/0.92         (((k8_relat_1 @ X48 @ X47) = (k5_relat_1 @ X47 @ (k6_relat_1 @ X48)))
% 0.72/0.92          | ~ (v1_relat_1 @ X47))),
% 0.72/0.92      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.72/0.92  thf(t76_relat_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ B ) =>
% 0.72/0.92       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.72/0.92         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.72/0.92  thf('25', plain,
% 0.72/0.92      (![X53 : $i, X54 : $i]:
% 0.72/0.92         ((r1_tarski @ (k5_relat_1 @ X53 @ (k6_relat_1 @ X54)) @ X53)
% 0.72/0.92          | ~ (v1_relat_1 @ X53))),
% 0.72/0.92      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.72/0.92  thf('26', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.72/0.92          | ~ (v1_relat_1 @ X0)
% 0.72/0.92          | ~ (v1_relat_1 @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['24', '25'])).
% 0.72/0.92  thf('27', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.72/0.92      inference('simplify', [status(thm)], ['26'])).
% 0.72/0.92  thf(t3_subset, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.92  thf('28', plain,
% 0.72/0.92      (![X37 : $i, X39 : $i]:
% 0.72/0.92         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 0.72/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.72/0.92  thf('29', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (v1_relat_1 @ X0)
% 0.72/0.92          | (m1_subset_1 @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['27', '28'])).
% 0.72/0.92  thf(cc2_relat_1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( v1_relat_1 @ A ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.72/0.92  thf('30', plain,
% 0.72/0.92      (![X40 : $i, X41 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.72/0.92          | (v1_relat_1 @ X40)
% 0.72/0.92          | ~ (v1_relat_1 @ X41))),
% 0.72/0.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.72/0.92  thf('31', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (v1_relat_1 @ X0)
% 0.72/0.92          | ~ (v1_relat_1 @ X0)
% 0.72/0.92          | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.92  thf('32', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.72/0.92      inference('simplify', [status(thm)], ['31'])).
% 0.72/0.92  thf('33', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (v1_relat_1 @ X0)
% 0.72/0.92          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.72/0.92              = (k8_relat_1 @ sk_A @ X0)))),
% 0.72/0.92      inference('clc', [status(thm)], ['23', '32'])).
% 0.72/0.92  thf('34', plain,
% 0.72/0.92      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.72/0.92         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('35', plain,
% 0.72/0.92      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.72/0.92        | ~ (v1_relat_1 @ sk_C))),
% 0.72/0.92      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.92  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('37', plain,
% 0.72/0.92      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.72/0.92      inference('demod', [status(thm)], ['35', '36'])).
% 0.72/0.92  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.72/0.92  
% 0.72/0.92  % SZS output end Refutation
% 0.72/0.92  
% 0.72/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
