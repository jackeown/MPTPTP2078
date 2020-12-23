%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WKmxBXng8Z

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:06 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   68 (  82 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  424 ( 562 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t214_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t214_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ ( k2_zfmisc_1 @ X43 @ X44 ) )
      | ~ ( r1_xboole_0 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X47: $i] :
      ( ( r1_tarski @ X47 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('10',plain,(
    ! [X48: $i] :
      ( ( ( k3_xboole_0 @ X48 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X48: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','28','31'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('33',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WKmxBXng8Z
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.69  % Solved by: fo/fo7.sh
% 0.49/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.69  % done 228 iterations in 0.241s
% 0.49/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.69  % SZS output start Refutation
% 0.49/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.49/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.69  thf(t214_relat_1, conjecture,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v1_relat_1 @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( v1_relat_1 @ B ) =>
% 0.49/0.69           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.49/0.69             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.69    (~( ![A:$i]:
% 0.49/0.69        ( ( v1_relat_1 @ A ) =>
% 0.49/0.69          ( ![B:$i]:
% 0.49/0.69            ( ( v1_relat_1 @ B ) =>
% 0.49/0.69              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.49/0.69                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.49/0.69    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 0.49/0.69  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('1', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t127_zfmisc_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.69     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.49/0.69       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.49/0.69  thf('2', plain,
% 0.49/0.69      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ (k2_zfmisc_1 @ X41 @ X42) @ (k2_zfmisc_1 @ X43 @ X44))
% 0.49/0.69          | ~ (r1_xboole_0 @ X41 @ X43))),
% 0.49/0.69      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.49/0.69  thf('3', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ X1) @ 
% 0.49/0.69          (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.69  thf(t21_relat_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v1_relat_1 @ A ) =>
% 0.49/0.69       ( r1_tarski @
% 0.49/0.69         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.49/0.69  thf('4', plain,
% 0.49/0.69      (![X47 : $i]:
% 0.49/0.69         ((r1_tarski @ X47 @ 
% 0.49/0.69           (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47)))
% 0.49/0.69          | ~ (v1_relat_1 @ X47))),
% 0.49/0.69      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.49/0.69  thf(t63_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.49/0.69       ( r1_xboole_0 @ A @ C ) ))).
% 0.49/0.69  thf('5', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.69          | ~ (r1_xboole_0 @ X8 @ X9)
% 0.49/0.69          | (r1_xboole_0 @ X7 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.49/0.69  thf('6', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X0)
% 0.49/0.69          | (r1_xboole_0 @ X0 @ X1)
% 0.49/0.69          | ~ (r1_xboole_0 @ 
% 0.49/0.69               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.69  thf('7', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['3', '6'])).
% 0.49/0.69  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('9', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (r1_xboole_0 @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf(t22_relat_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v1_relat_1 @ A ) =>
% 0.49/0.69       ( ( k3_xboole_0 @
% 0.49/0.69           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.49/0.69         ( A ) ) ))).
% 0.49/0.69  thf('10', plain,
% 0.49/0.69      (![X48 : $i]:
% 0.49/0.69         (((k3_xboole_0 @ X48 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))) = (
% 0.49/0.69            X48))
% 0.49/0.69          | ~ (v1_relat_1 @ X48))),
% 0.49/0.69      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.49/0.69  thf(t12_setfam_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.69  thf('11', plain,
% 0.49/0.69      (![X45 : $i, X46 : $i]:
% 0.49/0.69         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.49/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.69  thf('12', plain,
% 0.49/0.69      (![X48 : $i]:
% 0.49/0.69         (((k1_setfam_1 @ 
% 0.49/0.69            (k2_tarski @ X48 @ 
% 0.49/0.69             (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 0.49/0.69            = (X48))
% 0.49/0.69          | ~ (v1_relat_1 @ X48))),
% 0.49/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.49/0.69  thf(t100_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.69  thf('13', plain,
% 0.49/0.69      (![X1 : $i, X2 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.69           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf('14', plain,
% 0.49/0.69      (![X45 : $i, X46 : $i]:
% 0.49/0.69         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.49/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.69  thf('15', plain,
% 0.49/0.69      (![X1 : $i, X2 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.69           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 0.49/0.69      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.69  thf('16', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (((k4_xboole_0 @ X0 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.49/0.69            = (k5_xboole_0 @ X0 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['12', '15'])).
% 0.49/0.69  thf(t84_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.49/0.69          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.49/0.69  thf('17', plain,
% 0.49/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ X11 @ X12)
% 0.49/0.69          | ~ (r1_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69          | ~ (r1_xboole_0 @ X11 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.49/0.69  thf('18', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (r1_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (r1_xboole_0 @ X1 @ 
% 0.49/0.69               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.49/0.69          | (r1_xboole_0 @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf(t3_boole, axiom,
% 0.49/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.69  thf('19', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf(t48_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.69  thf('20', plain,
% 0.49/0.69      (![X5 : $i, X6 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.49/0.69           = (k3_xboole_0 @ X5 @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('21', plain,
% 0.49/0.69      (![X45 : $i, X46 : $i]:
% 0.49/0.69         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.49/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.69  thf('22', plain,
% 0.49/0.69      (![X5 : $i, X6 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.49/0.69           = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))),
% 0.49/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.49/0.69  thf('23', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X0 @ X0)
% 0.49/0.69           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['19', '22'])).
% 0.49/0.69  thf(idempotence_k3_xboole_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.49/0.69  thf('24', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.49/0.69  thf('25', plain,
% 0.49/0.69      (![X45 : $i, X46 : $i]:
% 0.49/0.69         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.49/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.69  thf('26', plain,
% 0.49/0.69      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.69  thf('27', plain,
% 0.49/0.69      (![X1 : $i, X2 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.69           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 0.49/0.69      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.69  thf('28', plain,
% 0.49/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.69  thf(t2_boole, axiom,
% 0.49/0.69    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.69  thf('29', plain,
% 0.49/0.69      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.69      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.69  thf('30', plain,
% 0.49/0.69      (![X45 : $i, X46 : $i]:
% 0.49/0.69         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.49/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.69  thf('31', plain,
% 0.49/0.69      (![X3 : $i]:
% 0.49/0.69         ((k1_setfam_1 @ (k2_tarski @ X3 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.49/0.69      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.69  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.69      inference('demod', [status(thm)], ['23', '28', '31'])).
% 0.49/0.69  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.49/0.69  thf('33', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.69  thf('34', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['32', '33'])).
% 0.49/0.69  thf('35', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (r1_xboole_0 @ X1 @ 
% 0.49/0.69               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.49/0.69          | (r1_xboole_0 @ X1 @ X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['18', '34'])).
% 0.49/0.69  thf('36', plain, (((r1_xboole_0 @ sk_A @ sk_B) | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.69      inference('sup-', [status(thm)], ['9', '35'])).
% 0.49/0.69  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('38', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.49/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.49/0.69  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
