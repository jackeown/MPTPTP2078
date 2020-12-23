%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TxKYwIbYCL

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:50 EST 2020

% Result     : Theorem 3.79s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  366 ( 477 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X24 @ X23 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X24 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X24 @ X23 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X24 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t28_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_relat_1])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TxKYwIbYCL
% 0.13/0.37  % Computer   : n025.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:11:51 EST 2020
% 0.22/0.37  % CPUTime    : 
% 0.22/0.37  % Running portfolio for 600 s
% 0.22/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.38  % Number of cores: 8
% 0.22/0.38  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 3.79/4.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.79/4.00  % Solved by: fo/fo7.sh
% 3.79/4.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.79/4.00  % done 4175 iterations in 3.517s
% 3.79/4.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.79/4.00  % SZS output start Refutation
% 3.79/4.00  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.79/4.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.79/4.00  thf(sk_B_type, type, sk_B: $i).
% 3.79/4.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.79/4.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.79/4.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.79/4.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.79/4.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.79/4.00  thf(sk_A_type, type, sk_A: $i).
% 3.79/4.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.79/4.00  thf(commutativity_k2_xboole_0, axiom,
% 3.79/4.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.79/4.00  thf('0', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.79/4.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.79/4.00  thf(t7_xboole_1, axiom,
% 3.79/4.00    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.79/4.00  thf('1', plain,
% 3.79/4.00      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 3.79/4.00      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.79/4.00  thf('2', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.79/4.00      inference('sup+', [status(thm)], ['0', '1'])).
% 3.79/4.00  thf(t43_xboole_1, axiom,
% 3.79/4.00    (![A:$i,B:$i,C:$i]:
% 3.79/4.00     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.79/4.00       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.79/4.00  thf('3', plain,
% 3.79/4.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.79/4.00         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 3.79/4.00          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 3.79/4.00      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.79/4.00  thf('4', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 3.79/4.00      inference('sup-', [status(thm)], ['2', '3'])).
% 3.79/4.00  thf(t3_subset, axiom,
% 3.79/4.00    (![A:$i,B:$i]:
% 3.79/4.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.79/4.00  thf('5', plain,
% 3.79/4.00      (![X14 : $i, X16 : $i]:
% 3.79/4.00         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 3.79/4.00      inference('cnf', [status(esa)], [t3_subset])).
% 3.79/4.00  thf('6', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.79/4.00      inference('sup-', [status(thm)], ['4', '5'])).
% 3.79/4.00  thf(cc2_relat_1, axiom,
% 3.79/4.00    (![A:$i]:
% 3.79/4.00     ( ( v1_relat_1 @ A ) =>
% 3.79/4.00       ( ![B:$i]:
% 3.79/4.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.79/4.00  thf('7', plain,
% 3.79/4.00      (![X17 : $i, X18 : $i]:
% 3.79/4.00         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.79/4.00          | (v1_relat_1 @ X17)
% 3.79/4.00          | ~ (v1_relat_1 @ X18))),
% 3.79/4.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.79/4.00  thf('8', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.79/4.00      inference('sup-', [status(thm)], ['6', '7'])).
% 3.79/4.00  thf(t26_relat_1, axiom,
% 3.79/4.00    (![A:$i]:
% 3.79/4.00     ( ( v1_relat_1 @ A ) =>
% 3.79/4.00       ( ![B:$i]:
% 3.79/4.00         ( ( v1_relat_1 @ B ) =>
% 3.79/4.00           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 3.79/4.00             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 3.79/4.00  thf('9', plain,
% 3.79/4.00      (![X23 : $i, X24 : $i]:
% 3.79/4.00         (~ (v1_relat_1 @ X23)
% 3.79/4.00          | ((k2_relat_1 @ (k2_xboole_0 @ X24 @ X23))
% 3.79/4.00              = (k2_xboole_0 @ (k2_relat_1 @ X24) @ (k2_relat_1 @ X23)))
% 3.79/4.00          | ~ (v1_relat_1 @ X24))),
% 3.79/4.00      inference('cnf', [status(esa)], [t26_relat_1])).
% 3.79/4.00  thf('10', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.79/4.00      inference('sup+', [status(thm)], ['0', '1'])).
% 3.79/4.00  thf('11', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.79/4.00           (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 3.79/4.00          | ~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ X0))),
% 3.79/4.00      inference('sup+', [status(thm)], ['9', '10'])).
% 3.79/4.00  thf(t39_xboole_1, axiom,
% 3.79/4.00    (![A:$i,B:$i]:
% 3.79/4.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.79/4.00  thf('12', plain,
% 3.79/4.00      (![X5 : $i, X6 : $i]:
% 3.79/4.00         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 3.79/4.00           = (k2_xboole_0 @ X5 @ X6))),
% 3.79/4.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.79/4.00  thf('13', plain,
% 3.79/4.00      (![X23 : $i, X24 : $i]:
% 3.79/4.00         (~ (v1_relat_1 @ X23)
% 3.79/4.00          | ((k2_relat_1 @ (k2_xboole_0 @ X24 @ X23))
% 3.79/4.00              = (k2_xboole_0 @ (k2_relat_1 @ X24) @ (k2_relat_1 @ X23)))
% 3.79/4.00          | ~ (v1_relat_1 @ X24))),
% 3.79/4.00      inference('cnf', [status(esa)], [t26_relat_1])).
% 3.79/4.00  thf('14', plain,
% 3.79/4.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.79/4.00         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 3.79/4.00          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 3.79/4.00      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.79/4.00  thf('15', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.79/4.00         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 3.79/4.00          | ~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ X0)
% 3.79/4.00          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 3.79/4.00             (k2_relat_1 @ X0)))),
% 3.79/4.00      inference('sup-', [status(thm)], ['13', '14'])).
% 3.79/4.00  thf('16', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.79/4.00         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 3.79/4.00          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 3.79/4.00             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 3.79/4.00          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 3.79/4.00          | ~ (v1_relat_1 @ X1))),
% 3.79/4.00      inference('sup-', [status(thm)], ['12', '15'])).
% 3.79/4.00  thf('17', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         (~ (v1_relat_1 @ X0)
% 3.79/4.00          | ~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 3.79/4.00          | (r1_tarski @ 
% 3.79/4.00             (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 3.79/4.00             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1))))),
% 3.79/4.00      inference('sup-', [status(thm)], ['11', '16'])).
% 3.79/4.00  thf('18', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 3.79/4.00           (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 3.79/4.00          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 3.79/4.00          | ~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ X0))),
% 3.79/4.00      inference('simplify', [status(thm)], ['17'])).
% 3.79/4.00  thf('19', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         (~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ X1)
% 3.79/4.00          | ~ (v1_relat_1 @ X0)
% 3.79/4.00          | (r1_tarski @ 
% 3.79/4.00             (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 3.79/4.00             (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.79/4.00      inference('sup-', [status(thm)], ['8', '18'])).
% 3.79/4.00  thf('20', plain,
% 3.79/4.00      (![X0 : $i, X1 : $i]:
% 3.79/4.00         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 3.79/4.00           (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)))
% 3.79/4.00          | ~ (v1_relat_1 @ X0)
% 3.79/4.00          | ~ (v1_relat_1 @ X1))),
% 3.79/4.00      inference('simplify', [status(thm)], ['19'])).
% 3.79/4.00  thf(t28_relat_1, conjecture,
% 3.79/4.00    (![A:$i]:
% 3.79/4.00     ( ( v1_relat_1 @ A ) =>
% 3.79/4.00       ( ![B:$i]:
% 3.79/4.00         ( ( v1_relat_1 @ B ) =>
% 3.79/4.00           ( r1_tarski @
% 3.79/4.00             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 3.79/4.00             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.79/4.00  thf(zf_stmt_0, negated_conjecture,
% 3.79/4.00    (~( ![A:$i]:
% 3.79/4.00        ( ( v1_relat_1 @ A ) =>
% 3.79/4.00          ( ![B:$i]:
% 3.79/4.00            ( ( v1_relat_1 @ B ) =>
% 3.79/4.00              ( r1_tarski @
% 3.79/4.00                ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 3.79/4.00                ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ) )),
% 3.79/4.00    inference('cnf.neg', [status(esa)], [t28_relat_1])).
% 3.79/4.00  thf('21', plain,
% 3.79/4.00      (~ (r1_tarski @ 
% 3.79/4.00          (k6_subset_1 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 3.79/4.00          (k2_relat_1 @ (k6_subset_1 @ sk_A @ sk_B)))),
% 3.79/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.79/4.00  thf(redefinition_k6_subset_1, axiom,
% 3.79/4.00    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.79/4.00  thf('22', plain,
% 3.79/4.00      (![X12 : $i, X13 : $i]:
% 3.79/4.00         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 3.79/4.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.79/4.00  thf('23', plain,
% 3.79/4.00      (![X12 : $i, X13 : $i]:
% 3.79/4.00         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 3.79/4.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.79/4.00  thf('24', plain,
% 3.79/4.00      (~ (r1_tarski @ 
% 3.79/4.00          (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 3.79/4.00          (k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 3.79/4.00      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.79/4.00  thf('25', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 3.79/4.00      inference('sup-', [status(thm)], ['20', '24'])).
% 3.79/4.00  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 3.79/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.79/4.00  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 3.79/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.79/4.00  thf('28', plain, ($false),
% 3.79/4.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 3.79/4.00  
% 3.79/4.00  % SZS output end Refutation
% 3.79/4.00  
% 3.79/4.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
