%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EKf1wIaiF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Theorem 54.08s
% Output     : Refutation 54.08s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  425 ( 673 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EKf1wIaiF
% 0.12/0.36  % Computer   : n003.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 14:10:57 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 54.08/54.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 54.08/54.29  % Solved by: fo/fo7.sh
% 54.08/54.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.08/54.29  % done 18538 iterations in 53.814s
% 54.08/54.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 54.08/54.29  % SZS output start Refutation
% 54.08/54.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 54.08/54.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 54.08/54.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.08/54.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 54.08/54.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 54.08/54.29  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 54.08/54.29  thf(sk_B_type, type, sk_B: $i).
% 54.08/54.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.08/54.29  thf(sk_C_type, type, sk_C: $i).
% 54.08/54.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.08/54.29  thf(sk_A_type, type, sk_A: $i).
% 54.08/54.29  thf(commutativity_k2_tarski, axiom,
% 54.08/54.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 54.08/54.29  thf('0', plain,
% 54.08/54.29      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 54.08/54.30      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 54.08/54.30  thf(t12_setfam_1, axiom,
% 54.08/54.30    (![A:$i,B:$i]:
% 54.08/54.30     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 54.08/54.30  thf('1', plain,
% 54.08/54.30      (![X7 : $i, X8 : $i]:
% 54.08/54.30         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 54.08/54.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.08/54.30  thf('2', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]:
% 54.08/54.30         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 54.08/54.30      inference('sup+', [status(thm)], ['0', '1'])).
% 54.08/54.30  thf('3', plain,
% 54.08/54.30      (![X7 : $i, X8 : $i]:
% 54.08/54.30         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 54.08/54.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.08/54.30  thf('4', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.08/54.30      inference('sup+', [status(thm)], ['2', '3'])).
% 54.08/54.30  thf(t17_xboole_1, axiom,
% 54.08/54.30    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 54.08/54.30  thf('5', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 54.08/54.30      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.08/54.30  thf(t3_subset, axiom,
% 54.08/54.30    (![A:$i,B:$i]:
% 54.08/54.30     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 54.08/54.30  thf('6', plain,
% 54.08/54.30      (![X9 : $i, X11 : $i]:
% 54.08/54.30         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 54.08/54.30      inference('cnf', [status(esa)], [t3_subset])).
% 54.08/54.30  thf('7', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]:
% 54.08/54.30         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 54.08/54.30      inference('sup-', [status(thm)], ['5', '6'])).
% 54.08/54.30  thf(cc2_relat_1, axiom,
% 54.08/54.30    (![A:$i]:
% 54.08/54.30     ( ( v1_relat_1 @ A ) =>
% 54.08/54.30       ( ![B:$i]:
% 54.08/54.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 54.08/54.30  thf('8', plain,
% 54.08/54.30      (![X12 : $i, X13 : $i]:
% 54.08/54.30         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 54.08/54.30          | (v1_relat_1 @ X12)
% 54.08/54.30          | ~ (v1_relat_1 @ X13))),
% 54.08/54.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 54.08/54.30  thf('9', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 54.08/54.30      inference('sup-', [status(thm)], ['7', '8'])).
% 54.08/54.30  thf('10', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]:
% 54.08/54.30         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 54.08/54.30      inference('sup+', [status(thm)], ['4', '9'])).
% 54.08/54.30  thf('11', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.08/54.30      inference('sup+', [status(thm)], ['2', '3'])).
% 54.08/54.30  thf('12', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 54.08/54.30      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.08/54.30  thf('13', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 54.08/54.30      inference('sup+', [status(thm)], ['11', '12'])).
% 54.08/54.30  thf(t48_relat_1, axiom,
% 54.08/54.30    (![A:$i]:
% 54.08/54.30     ( ( v1_relat_1 @ A ) =>
% 54.08/54.30       ( ![B:$i]:
% 54.08/54.30         ( ( v1_relat_1 @ B ) =>
% 54.08/54.30           ( ![C:$i]:
% 54.08/54.30             ( ( v1_relat_1 @ C ) =>
% 54.08/54.30               ( ( r1_tarski @ A @ B ) =>
% 54.08/54.30                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 54.08/54.30  thf('14', plain,
% 54.08/54.30      (![X14 : $i, X15 : $i, X16 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X14)
% 54.08/54.30          | ~ (r1_tarski @ X15 @ X14)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X16 @ X15) @ (k5_relat_1 @ X16 @ X14))
% 54.08/54.30          | ~ (v1_relat_1 @ X16)
% 54.08/54.30          | ~ (v1_relat_1 @ X15))),
% 54.08/54.30      inference('cnf', [status(esa)], [t48_relat_1])).
% 54.08/54.30  thf('15', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 54.08/54.30          | ~ (v1_relat_1 @ X2)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 54.08/54.30             (k5_relat_1 @ X2 @ X0))
% 54.08/54.30          | ~ (v1_relat_1 @ X0))),
% 54.08/54.30      inference('sup-', [status(thm)], ['13', '14'])).
% 54.08/54.30  thf('16', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X0)
% 54.08/54.30          | ~ (v1_relat_1 @ X0)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 54.08/54.30             (k5_relat_1 @ X2 @ X0))
% 54.08/54.30          | ~ (v1_relat_1 @ X2))),
% 54.08/54.30      inference('sup-', [status(thm)], ['10', '15'])).
% 54.08/54.30  thf('17', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X2)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 54.08/54.30             (k5_relat_1 @ X2 @ X0))
% 54.08/54.30          | ~ (v1_relat_1 @ X0))),
% 54.08/54.30      inference('simplify', [status(thm)], ['16'])).
% 54.08/54.30  thf('18', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 54.08/54.30      inference('sup-', [status(thm)], ['7', '8'])).
% 54.08/54.30  thf('19', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 54.08/54.30      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.08/54.30  thf('20', plain,
% 54.08/54.30      (![X14 : $i, X15 : $i, X16 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X14)
% 54.08/54.30          | ~ (r1_tarski @ X15 @ X14)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X16 @ X15) @ (k5_relat_1 @ X16 @ X14))
% 54.08/54.30          | ~ (v1_relat_1 @ X16)
% 54.08/54.30          | ~ (v1_relat_1 @ X15))),
% 54.08/54.30      inference('cnf', [status(esa)], [t48_relat_1])).
% 54.08/54.30  thf('21', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 54.08/54.30          | ~ (v1_relat_1 @ X2)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 54.08/54.30             (k5_relat_1 @ X2 @ X0))
% 54.08/54.30          | ~ (v1_relat_1 @ X0))),
% 54.08/54.30      inference('sup-', [status(thm)], ['19', '20'])).
% 54.08/54.30  thf('22', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X1)
% 54.08/54.30          | ~ (v1_relat_1 @ X1)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 54.08/54.30             (k5_relat_1 @ X2 @ X1))
% 54.08/54.30          | ~ (v1_relat_1 @ X2))),
% 54.08/54.30      inference('sup-', [status(thm)], ['18', '21'])).
% 54.08/54.30  thf('23', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X2)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 54.08/54.30             (k5_relat_1 @ X2 @ X1))
% 54.08/54.30          | ~ (v1_relat_1 @ X1))),
% 54.08/54.30      inference('simplify', [status(thm)], ['22'])).
% 54.08/54.30  thf(t19_xboole_1, axiom,
% 54.08/54.30    (![A:$i,B:$i,C:$i]:
% 54.08/54.30     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 54.08/54.30       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 54.08/54.30  thf('24', plain,
% 54.08/54.30      (![X2 : $i, X3 : $i, X4 : $i]:
% 54.08/54.30         (~ (r1_tarski @ X2 @ X3)
% 54.08/54.30          | ~ (r1_tarski @ X2 @ X4)
% 54.08/54.30          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 54.08/54.30      inference('cnf', [status(esa)], [t19_xboole_1])).
% 54.08/54.30  thf('25', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X0)
% 54.08/54.30          | ~ (v1_relat_1 @ X1)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 54.08/54.30             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 54.08/54.30          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 54.08/54.30      inference('sup-', [status(thm)], ['23', '24'])).
% 54.08/54.30  thf('26', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X0)
% 54.08/54.30          | ~ (v1_relat_1 @ X1)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 54.08/54.30             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 54.08/54.30          | ~ (v1_relat_1 @ X1)
% 54.08/54.30          | ~ (v1_relat_1 @ X2))),
% 54.08/54.30      inference('sup-', [status(thm)], ['17', '25'])).
% 54.08/54.30  thf('27', plain,
% 54.08/54.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.08/54.30         (~ (v1_relat_1 @ X2)
% 54.08/54.30          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 54.08/54.30             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 54.08/54.30          | ~ (v1_relat_1 @ X1)
% 54.08/54.30          | ~ (v1_relat_1 @ X0))),
% 54.08/54.30      inference('simplify', [status(thm)], ['26'])).
% 54.08/54.30  thf(t52_relat_1, conjecture,
% 54.08/54.30    (![A:$i]:
% 54.08/54.30     ( ( v1_relat_1 @ A ) =>
% 54.08/54.30       ( ![B:$i]:
% 54.08/54.30         ( ( v1_relat_1 @ B ) =>
% 54.08/54.30           ( ![C:$i]:
% 54.08/54.30             ( ( v1_relat_1 @ C ) =>
% 54.08/54.30               ( r1_tarski @
% 54.08/54.30                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 54.08/54.30                 ( k3_xboole_0 @
% 54.08/54.30                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 54.08/54.30  thf(zf_stmt_0, negated_conjecture,
% 54.08/54.30    (~( ![A:$i]:
% 54.08/54.30        ( ( v1_relat_1 @ A ) =>
% 54.08/54.30          ( ![B:$i]:
% 54.08/54.30            ( ( v1_relat_1 @ B ) =>
% 54.08/54.30              ( ![C:$i]:
% 54.08/54.30                ( ( v1_relat_1 @ C ) =>
% 54.08/54.30                  ( r1_tarski @
% 54.08/54.30                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 54.08/54.30                    ( k3_xboole_0 @
% 54.08/54.30                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 54.08/54.30    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 54.08/54.30  thf('28', plain,
% 54.08/54.30      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 54.08/54.30          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 54.08/54.30           (k5_relat_1 @ sk_A @ sk_C)))),
% 54.08/54.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.08/54.30  thf('29', plain,
% 54.08/54.30      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 54.08/54.30      inference('sup-', [status(thm)], ['27', '28'])).
% 54.08/54.30  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 54.08/54.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.08/54.30  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 54.08/54.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.08/54.30  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 54.08/54.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.08/54.30  thf('33', plain, ($false),
% 54.08/54.30      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 54.08/54.30  
% 54.08/54.30  % SZS output end Refutation
% 54.08/54.30  
% 54.08/54.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
