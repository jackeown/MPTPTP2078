%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IS9XP8GVCh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:04 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 ( 460 expanded)
%              Number of equality atoms :    3 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( r1_tarski @ ( k3_relat_1 @ X46 ) @ ( k3_relat_1 @ X45 ) )
      | ~ ( r1_tarski @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['6','11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( r1_tarski @ ( k3_relat_1 @ X46 ) @ ( k3_relat_1 @ X45 ) )
      | ~ ( r1_tarski @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','20'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IS9XP8GVCh
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.72  % Solved by: fo/fo7.sh
% 0.45/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.72  % done 440 iterations in 0.255s
% 0.45/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.72  % SZS output start Refutation
% 0.45/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.72  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.72  thf(idempotence_k2_xboole_0, axiom,
% 0.45/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.72  thf('0', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.72      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.72  thf(t31_xboole_1, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( r1_tarski @
% 0.45/0.72       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.45/0.72       ( k2_xboole_0 @ B @ C ) ))).
% 0.45/0.72  thf('1', plain,
% 0.45/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.72         (r1_tarski @ 
% 0.45/0.72          (k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X8)) @ 
% 0.45/0.72          (k2_xboole_0 @ X7 @ X8))),
% 0.45/0.72      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.45/0.72  thf('2', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.45/0.72      inference('sup+', [status(thm)], ['0', '1'])).
% 0.45/0.72  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.72      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.72  thf('4', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.72  thf(t31_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ![B:$i]:
% 0.45/0.72         ( ( v1_relat_1 @ B ) =>
% 0.45/0.72           ( ( r1_tarski @ A @ B ) =>
% 0.45/0.72             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.45/0.72  thf('5', plain,
% 0.45/0.72      (![X45 : $i, X46 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X45)
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ X46) @ (k3_relat_1 @ X45))
% 0.45/0.72          | ~ (r1_tarski @ X46 @ X45)
% 0.45/0.72          | ~ (v1_relat_1 @ X46))),
% 0.45/0.72      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.45/0.72  thf('6', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.72             (k3_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.72  thf('7', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.72  thf(t3_subset, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.72  thf('8', plain,
% 0.45/0.72      (![X40 : $i, X42 : $i]:
% 0.45/0.72         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 0.45/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.72  thf('9', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.72  thf(cc2_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ![B:$i]:
% 0.45/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.72  thf('10', plain,
% 0.45/0.72      (![X43 : $i, X44 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.45/0.72          | (v1_relat_1 @ X43)
% 0.45/0.72          | ~ (v1_relat_1 @ X44))),
% 0.45/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.72  thf('11', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.72  thf('12', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.72             (k3_relat_1 @ X0)))),
% 0.45/0.72      inference('clc', [status(thm)], ['6', '11'])).
% 0.45/0.72  thf(t17_xboole_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.72  thf('13', plain,
% 0.45/0.72      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.45/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.72  thf('14', plain,
% 0.45/0.72      (![X45 : $i, X46 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X45)
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ X46) @ (k3_relat_1 @ X45))
% 0.45/0.72          | ~ (r1_tarski @ X46 @ X45)
% 0.45/0.72          | ~ (v1_relat_1 @ X46))),
% 0.45/0.72      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.45/0.72  thf('15', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.45/0.72             (k3_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.72  thf('16', plain,
% 0.45/0.72      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.45/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.72  thf('17', plain,
% 0.45/0.72      (![X40 : $i, X42 : $i]:
% 0.45/0.72         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 0.45/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.72  thf('18', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.72  thf('19', plain,
% 0.45/0.72      (![X43 : $i, X44 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.45/0.72          | (v1_relat_1 @ X43)
% 0.45/0.72          | ~ (v1_relat_1 @ X44))),
% 0.45/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.72  thf('20', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.72  thf('21', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.45/0.72             (k3_relat_1 @ X0)))),
% 0.45/0.72      inference('clc', [status(thm)], ['15', '20'])).
% 0.45/0.72  thf(t19_xboole_1, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.45/0.72       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.72  thf('22', plain,
% 0.45/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.72         (~ (r1_tarski @ X3 @ X4)
% 0.45/0.72          | ~ (r1_tarski @ X3 @ X5)
% 0.45/0.72          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.45/0.72      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.45/0.72  thf('23', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.45/0.72             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.45/0.72          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.45/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.72  thf('24', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.72             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.45/0.72          | ~ (v1_relat_1 @ X1))),
% 0.45/0.72      inference('sup-', [status(thm)], ['12', '23'])).
% 0.45/0.72  thf(t34_relat_1, conjecture,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ![B:$i]:
% 0.45/0.72         ( ( v1_relat_1 @ B ) =>
% 0.45/0.72           ( r1_tarski @
% 0.45/0.72             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.45/0.72             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.72    (~( ![A:$i]:
% 0.45/0.72        ( ( v1_relat_1 @ A ) =>
% 0.45/0.72          ( ![B:$i]:
% 0.45/0.72            ( ( v1_relat_1 @ B ) =>
% 0.45/0.72              ( r1_tarski @
% 0.45/0.72                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.45/0.72                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.45/0.72    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.45/0.72  thf('25', plain,
% 0.45/0.72      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.45/0.72          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('26', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.72  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('29', plain, ($false),
% 0.45/0.72      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.45/0.72  
% 0.45/0.72  % SZS output end Refutation
% 0.45/0.72  
% 0.57/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
