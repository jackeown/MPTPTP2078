%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sHLE87G9TO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:38 EST 2020

% Result     : Theorem 44.49s
% Output     : Refutation 44.49s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 112 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 806 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X23 @ X22 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X23 ) @ ( k1_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','24'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t14_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_relat_1])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['32','33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sHLE87G9TO
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 44.49/44.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.49/44.69  % Solved by: fo/fo7.sh
% 44.49/44.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.49/44.69  % done 23260 iterations in 44.246s
% 44.49/44.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.49/44.69  % SZS output start Refutation
% 44.49/44.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 44.49/44.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.49/44.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 44.49/44.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 44.49/44.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 44.49/44.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.49/44.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 44.49/44.69  thf(sk_A_type, type, sk_A: $i).
% 44.49/44.69  thf(sk_B_type, type, sk_B: $i).
% 44.49/44.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.49/44.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 44.49/44.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 44.49/44.69  thf(commutativity_k2_tarski, axiom,
% 44.49/44.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 44.49/44.69  thf('0', plain,
% 44.49/44.69      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 44.49/44.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.49/44.69  thf(t12_setfam_1, axiom,
% 44.49/44.69    (![A:$i,B:$i]:
% 44.49/44.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 44.49/44.69  thf('1', plain,
% 44.49/44.69      (![X15 : $i, X16 : $i]:
% 44.49/44.69         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 44.49/44.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 44.49/44.69  thf('2', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 44.49/44.69      inference('sup+', [status(thm)], ['0', '1'])).
% 44.49/44.69  thf('3', plain,
% 44.49/44.69      (![X15 : $i, X16 : $i]:
% 44.49/44.69         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 44.49/44.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 44.49/44.69  thf('4', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.49/44.69      inference('sup+', [status(thm)], ['2', '3'])).
% 44.49/44.69  thf(t17_xboole_1, axiom,
% 44.49/44.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 44.49/44.69  thf('5', plain,
% 44.49/44.69      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 44.49/44.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 44.49/44.69  thf(t12_xboole_1, axiom,
% 44.49/44.69    (![A:$i,B:$i]:
% 44.49/44.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 44.49/44.69  thf('6', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 44.49/44.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 44.49/44.69  thf('7', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 44.49/44.69      inference('sup-', [status(thm)], ['5', '6'])).
% 44.49/44.69  thf('8', plain,
% 44.49/44.69      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 44.49/44.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.49/44.69  thf(l51_zfmisc_1, axiom,
% 44.49/44.69    (![A:$i,B:$i]:
% 44.49/44.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 44.49/44.69  thf('9', plain,
% 44.49/44.69      (![X13 : $i, X14 : $i]:
% 44.49/44.69         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 44.49/44.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.49/44.69  thf('10', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.69      inference('sup+', [status(thm)], ['8', '9'])).
% 44.49/44.69  thf('11', plain,
% 44.49/44.69      (![X13 : $i, X14 : $i]:
% 44.49/44.69         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 44.49/44.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.49/44.69  thf('12', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.69      inference('sup+', [status(thm)], ['10', '11'])).
% 44.49/44.69  thf('13', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 44.49/44.69      inference('demod', [status(thm)], ['7', '12'])).
% 44.49/44.69  thf(t13_relat_1, axiom,
% 44.49/44.69    (![A:$i]:
% 44.49/44.69     ( ( v1_relat_1 @ A ) =>
% 44.49/44.69       ( ![B:$i]:
% 44.49/44.69         ( ( v1_relat_1 @ B ) =>
% 44.49/44.69           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 44.49/44.69             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 44.49/44.69  thf('14', plain,
% 44.49/44.69      (![X22 : $i, X23 : $i]:
% 44.49/44.69         (~ (v1_relat_1 @ X22)
% 44.49/44.69          | ((k1_relat_1 @ (k2_xboole_0 @ X23 @ X22))
% 44.49/44.69              = (k2_xboole_0 @ (k1_relat_1 @ X23) @ (k1_relat_1 @ X22)))
% 44.49/44.69          | ~ (v1_relat_1 @ X23))),
% 44.49/44.69      inference('cnf', [status(esa)], [t13_relat_1])).
% 44.49/44.69  thf('15', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.69      inference('sup+', [status(thm)], ['10', '11'])).
% 44.49/44.69  thf(t7_xboole_1, axiom,
% 44.49/44.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 44.49/44.69  thf('16', plain,
% 44.49/44.69      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 44.49/44.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 44.49/44.69  thf('17', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 44.49/44.69      inference('sup+', [status(thm)], ['15', '16'])).
% 44.49/44.69  thf('18', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 44.49/44.69           (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 44.49/44.69          | ~ (v1_relat_1 @ X1)
% 44.49/44.69          | ~ (v1_relat_1 @ X0))),
% 44.49/44.69      inference('sup+', [status(thm)], ['14', '17'])).
% 44.49/44.69  thf('19', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 44.49/44.69           (k1_relat_1 @ X0))
% 44.49/44.69          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 44.49/44.69          | ~ (v1_relat_1 @ X0))),
% 44.49/44.69      inference('sup+', [status(thm)], ['13', '18'])).
% 44.49/44.69  thf('20', plain,
% 44.49/44.69      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 44.49/44.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 44.49/44.69  thf(t3_subset, axiom,
% 44.49/44.69    (![A:$i,B:$i]:
% 44.49/44.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 44.49/44.69  thf('21', plain,
% 44.49/44.69      (![X17 : $i, X19 : $i]:
% 44.49/44.69         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 44.49/44.69      inference('cnf', [status(esa)], [t3_subset])).
% 44.49/44.69  thf('22', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 44.49/44.69      inference('sup-', [status(thm)], ['20', '21'])).
% 44.49/44.69  thf(cc2_relat_1, axiom,
% 44.49/44.69    (![A:$i]:
% 44.49/44.69     ( ( v1_relat_1 @ A ) =>
% 44.49/44.69       ( ![B:$i]:
% 44.49/44.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 44.49/44.69  thf('23', plain,
% 44.49/44.69      (![X20 : $i, X21 : $i]:
% 44.49/44.69         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 44.49/44.69          | (v1_relat_1 @ X20)
% 44.49/44.69          | ~ (v1_relat_1 @ X21))),
% 44.49/44.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 44.49/44.69  thf('24', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 44.49/44.69      inference('sup-', [status(thm)], ['22', '23'])).
% 44.49/44.69  thf('25', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         (~ (v1_relat_1 @ X0)
% 44.49/44.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 44.49/44.69             (k1_relat_1 @ X0)))),
% 44.49/44.69      inference('clc', [status(thm)], ['19', '24'])).
% 44.49/44.69  thf('26', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.49/44.69           (k1_relat_1 @ X0))
% 44.49/44.69          | ~ (v1_relat_1 @ X0))),
% 44.49/44.69      inference('sup+', [status(thm)], ['4', '25'])).
% 44.49/44.69  thf('27', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         (~ (v1_relat_1 @ X0)
% 44.49/44.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 44.49/44.69             (k1_relat_1 @ X0)))),
% 44.49/44.69      inference('clc', [status(thm)], ['19', '24'])).
% 44.49/44.69  thf(t19_xboole_1, axiom,
% 44.49/44.69    (![A:$i,B:$i,C:$i]:
% 44.49/44.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 44.49/44.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 44.49/44.69  thf('28', plain,
% 44.49/44.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 44.49/44.69         (~ (r1_tarski @ X4 @ X5)
% 44.49/44.69          | ~ (r1_tarski @ X4 @ X6)
% 44.49/44.69          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 44.49/44.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 44.49/44.69  thf('29', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.69         (~ (v1_relat_1 @ X0)
% 44.49/44.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 44.49/44.69             (k3_xboole_0 @ (k1_relat_1 @ X0) @ X2))
% 44.49/44.69          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 44.49/44.69      inference('sup-', [status(thm)], ['27', '28'])).
% 44.49/44.69  thf('30', plain,
% 44.49/44.69      (![X0 : $i, X1 : $i]:
% 44.49/44.69         (~ (v1_relat_1 @ X0)
% 44.49/44.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.49/44.69             (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 44.49/44.69          | ~ (v1_relat_1 @ X1))),
% 44.49/44.69      inference('sup-', [status(thm)], ['26', '29'])).
% 44.49/44.69  thf(t14_relat_1, conjecture,
% 44.49/44.69    (![A:$i]:
% 44.49/44.69     ( ( v1_relat_1 @ A ) =>
% 44.49/44.69       ( ![B:$i]:
% 44.49/44.69         ( ( v1_relat_1 @ B ) =>
% 44.49/44.69           ( r1_tarski @
% 44.49/44.69             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 44.49/44.69             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 44.49/44.69  thf(zf_stmt_0, negated_conjecture,
% 44.49/44.69    (~( ![A:$i]:
% 44.49/44.69        ( ( v1_relat_1 @ A ) =>
% 44.49/44.69          ( ![B:$i]:
% 44.49/44.69            ( ( v1_relat_1 @ B ) =>
% 44.49/44.69              ( r1_tarski @
% 44.49/44.69                ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 44.49/44.69                ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 44.49/44.69    inference('cnf.neg', [status(esa)], [t14_relat_1])).
% 44.49/44.69  thf('31', plain,
% 44.49/44.69      (~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 44.49/44.69          (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 44.49/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.49/44.69  thf('32', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 44.49/44.69      inference('sup-', [status(thm)], ['30', '31'])).
% 44.49/44.69  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 44.49/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.49/44.69  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 44.49/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.49/44.69  thf('35', plain, ($false),
% 44.49/44.69      inference('demod', [status(thm)], ['32', '33', '34'])).
% 44.49/44.69  
% 44.49/44.69  % SZS output end Refutation
% 44.49/44.69  
% 44.52/44.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
