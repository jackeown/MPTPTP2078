%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D3TOasf2NC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Timeout 59.63s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  399 ( 578 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

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

thf('26',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D3TOasf2NC
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 59.63/59.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 59.63/59.88  % Solved by: fo/fo7.sh
% 59.63/59.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.63/59.88  % done 18538 iterations in 59.416s
% 59.63/59.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 59.63/59.88  % SZS output start Refutation
% 59.63/59.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.63/59.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 59.63/59.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 59.63/59.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 59.63/59.88  thf(sk_B_type, type, sk_B: $i).
% 59.63/59.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 59.63/59.88  thf(sk_C_type, type, sk_C: $i).
% 59.63/59.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 59.63/59.88  thf(sk_A_type, type, sk_A: $i).
% 59.63/59.88  thf(commutativity_k3_xboole_0, axiom,
% 59.63/59.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 59.63/59.88  thf('0', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.63/59.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.63/59.88  thf(t17_xboole_1, axiom,
% 59.63/59.88    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 59.63/59.88  thf('1', plain,
% 59.63/59.88      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 59.63/59.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 59.63/59.88  thf('2', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 59.63/59.88      inference('sup+', [status(thm)], ['0', '1'])).
% 59.63/59.88  thf(t3_subset, axiom,
% 59.63/59.88    (![A:$i,B:$i]:
% 59.63/59.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 59.63/59.88  thf('3', plain,
% 59.63/59.88      (![X9 : $i, X11 : $i]:
% 59.63/59.88         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 59.63/59.88      inference('cnf', [status(esa)], [t3_subset])).
% 59.63/59.88  thf('4', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]:
% 59.63/59.88         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 59.63/59.88      inference('sup-', [status(thm)], ['2', '3'])).
% 59.63/59.88  thf(cc2_relat_1, axiom,
% 59.63/59.88    (![A:$i]:
% 59.63/59.88     ( ( v1_relat_1 @ A ) =>
% 59.63/59.88       ( ![B:$i]:
% 59.63/59.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 59.63/59.88  thf('5', plain,
% 59.63/59.88      (![X12 : $i, X13 : $i]:
% 59.63/59.88         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 59.63/59.88          | (v1_relat_1 @ X12)
% 59.63/59.88          | ~ (v1_relat_1 @ X13))),
% 59.63/59.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 59.63/59.88  thf('6', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 59.63/59.88      inference('sup-', [status(thm)], ['4', '5'])).
% 59.63/59.88  thf('7', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 59.63/59.88      inference('sup+', [status(thm)], ['0', '1'])).
% 59.63/59.88  thf(t48_relat_1, axiom,
% 59.63/59.88    (![A:$i]:
% 59.63/59.88     ( ( v1_relat_1 @ A ) =>
% 59.63/59.88       ( ![B:$i]:
% 59.63/59.88         ( ( v1_relat_1 @ B ) =>
% 59.63/59.88           ( ![C:$i]:
% 59.63/59.88             ( ( v1_relat_1 @ C ) =>
% 59.63/59.88               ( ( r1_tarski @ A @ B ) =>
% 59.63/59.88                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 59.63/59.88  thf('8', plain,
% 59.63/59.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ X14)
% 59.63/59.88          | ~ (r1_tarski @ X15 @ X14)
% 59.63/59.88          | (r1_tarski @ (k5_relat_1 @ X16 @ X15) @ (k5_relat_1 @ X16 @ X14))
% 59.63/59.88          | ~ (v1_relat_1 @ X16)
% 59.63/59.88          | ~ (v1_relat_1 @ X15))),
% 59.63/59.88      inference('cnf', [status(esa)], [t48_relat_1])).
% 59.63/59.88  thf('9', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 59.63/59.88          | ~ (v1_relat_1 @ X2)
% 59.63/59.88          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 59.63/59.88             (k5_relat_1 @ X2 @ X0))
% 59.63/59.88          | ~ (v1_relat_1 @ X0))),
% 59.63/59.88      inference('sup-', [status(thm)], ['7', '8'])).
% 59.63/59.88  thf('10', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ X0)
% 59.63/59.88          | ~ (v1_relat_1 @ X0)
% 59.63/59.88          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 59.63/59.88             (k5_relat_1 @ X2 @ X0))
% 59.63/59.88          | ~ (v1_relat_1 @ X2))),
% 59.63/59.88      inference('sup-', [status(thm)], ['6', '9'])).
% 59.63/59.88  thf('11', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ X2)
% 59.63/59.88          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 59.63/59.88             (k5_relat_1 @ X2 @ X0))
% 59.63/59.88          | ~ (v1_relat_1 @ X0))),
% 59.63/59.88      inference('simplify', [status(thm)], ['10'])).
% 59.63/59.88  thf('12', plain,
% 59.63/59.88      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 59.63/59.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 59.63/59.88  thf('13', plain,
% 59.63/59.88      (![X9 : $i, X11 : $i]:
% 59.63/59.88         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 59.63/59.88      inference('cnf', [status(esa)], [t3_subset])).
% 59.63/59.88  thf('14', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]:
% 59.63/59.88         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 59.63/59.88      inference('sup-', [status(thm)], ['12', '13'])).
% 59.63/59.88  thf('15', plain,
% 59.63/59.88      (![X12 : $i, X13 : $i]:
% 59.63/59.88         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 59.63/59.88          | (v1_relat_1 @ X12)
% 59.63/59.88          | ~ (v1_relat_1 @ X13))),
% 59.63/59.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 59.63/59.88  thf('16', plain,
% 59.63/59.88      (![X0 : $i, X1 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 59.63/59.88      inference('sup-', [status(thm)], ['14', '15'])).
% 59.63/59.88  thf('17', plain,
% 59.63/59.88      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 59.63/59.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 59.63/59.88  thf('18', plain,
% 59.63/59.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 59.63/59.88         (~ (v1_relat_1 @ X14)
% 59.63/59.88          | ~ (r1_tarski @ X15 @ X14)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X16 @ X15) @ (k5_relat_1 @ X16 @ X14))
% 59.63/59.89          | ~ (v1_relat_1 @ X16)
% 59.63/59.89          | ~ (v1_relat_1 @ X15))),
% 59.63/59.89      inference('cnf', [status(esa)], [t48_relat_1])).
% 59.63/59.89  thf('19', plain,
% 59.63/59.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.89         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 59.63/59.89          | ~ (v1_relat_1 @ X2)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 59.63/59.89             (k5_relat_1 @ X2 @ X0))
% 59.63/59.89          | ~ (v1_relat_1 @ X0))),
% 59.63/59.89      inference('sup-', [status(thm)], ['17', '18'])).
% 59.63/59.89  thf('20', plain,
% 59.63/59.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.89         (~ (v1_relat_1 @ X1)
% 59.63/59.89          | ~ (v1_relat_1 @ X1)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 59.63/59.89             (k5_relat_1 @ X2 @ X1))
% 59.63/59.89          | ~ (v1_relat_1 @ X2))),
% 59.63/59.89      inference('sup-', [status(thm)], ['16', '19'])).
% 59.63/59.89  thf('21', plain,
% 59.63/59.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.89         (~ (v1_relat_1 @ X2)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 59.63/59.89             (k5_relat_1 @ X2 @ X1))
% 59.63/59.89          | ~ (v1_relat_1 @ X1))),
% 59.63/59.89      inference('simplify', [status(thm)], ['20'])).
% 59.63/59.89  thf(t19_xboole_1, axiom,
% 59.63/59.89    (![A:$i,B:$i,C:$i]:
% 59.63/59.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 59.63/59.89       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 59.63/59.89  thf('22', plain,
% 59.63/59.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 59.63/59.89         (~ (r1_tarski @ X4 @ X5)
% 59.63/59.89          | ~ (r1_tarski @ X4 @ X6)
% 59.63/59.89          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 59.63/59.89      inference('cnf', [status(esa)], [t19_xboole_1])).
% 59.63/59.89  thf('23', plain,
% 59.63/59.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.63/59.89         (~ (v1_relat_1 @ X0)
% 59.63/59.89          | ~ (v1_relat_1 @ X1)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 59.63/59.89             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 59.63/59.89          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 59.63/59.89      inference('sup-', [status(thm)], ['21', '22'])).
% 59.63/59.89  thf('24', plain,
% 59.63/59.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.89         (~ (v1_relat_1 @ X0)
% 59.63/59.89          | ~ (v1_relat_1 @ X1)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 59.63/59.89             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 59.63/59.89          | ~ (v1_relat_1 @ X1)
% 59.63/59.89          | ~ (v1_relat_1 @ X2))),
% 59.63/59.89      inference('sup-', [status(thm)], ['11', '23'])).
% 59.63/59.89  thf('25', plain,
% 59.63/59.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.63/59.89         (~ (v1_relat_1 @ X2)
% 59.63/59.89          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 59.63/59.89             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 59.63/59.89          | ~ (v1_relat_1 @ X1)
% 59.63/59.89          | ~ (v1_relat_1 @ X0))),
% 59.63/59.89      inference('simplify', [status(thm)], ['24'])).
% 59.63/59.89  thf(t52_relat_1, conjecture,
% 59.63/59.89    (![A:$i]:
% 59.63/59.89     ( ( v1_relat_1 @ A ) =>
% 59.63/59.89       ( ![B:$i]:
% 59.63/59.89         ( ( v1_relat_1 @ B ) =>
% 59.63/59.89           ( ![C:$i]:
% 59.63/59.89             ( ( v1_relat_1 @ C ) =>
% 59.63/59.89               ( r1_tarski @
% 59.63/59.89                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 59.63/59.89                 ( k3_xboole_0 @
% 59.63/59.89                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 59.63/59.89  thf(zf_stmt_0, negated_conjecture,
% 59.63/59.89    (~( ![A:$i]:
% 59.63/59.89        ( ( v1_relat_1 @ A ) =>
% 59.63/59.89          ( ![B:$i]:
% 59.63/59.89            ( ( v1_relat_1 @ B ) =>
% 59.63/59.89              ( ![C:$i]:
% 59.63/59.89                ( ( v1_relat_1 @ C ) =>
% 59.63/59.89                  ( r1_tarski @
% 59.63/59.89                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 59.63/59.89                    ( k3_xboole_0 @
% 59.63/59.89                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 59.63/59.89    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 59.63/59.89  thf('26', plain,
% 59.63/59.89      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 59.63/59.89          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 59.63/59.89           (k5_relat_1 @ sk_A @ sk_C)))),
% 59.63/59.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.63/59.89  thf('27', plain,
% 59.63/59.89      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 59.63/59.89      inference('sup-', [status(thm)], ['25', '26'])).
% 59.63/59.89  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 59.63/59.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.63/59.89  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 59.63/59.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.63/59.89  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 59.63/59.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.63/59.89  thf('31', plain, ($false),
% 59.63/59.89      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 59.63/59.89  
% 59.63/59.89  % SZS output end Refutation
% 59.63/59.89  
% 59.63/59.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
