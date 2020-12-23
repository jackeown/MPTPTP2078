%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WEDraHcBY2

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 ( 550 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t62_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( ( v3_setfam_1 @ B @ A )
              & ( r1_tarski @ C @ B ) )
           => ( v3_setfam_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( ( v3_setfam_1 @ B @ A )
                & ( r1_tarski @ C @ B ) )
             => ( v3_setfam_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v3_setfam_1 @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ( v3_setfam_1 @ sk_C @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_setfam_1 @ X6 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_setfam_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_setfam_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['18','23'])).

thf('25',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['11','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['6','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WEDraHcBY2
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 39 iterations in 0.017s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(t62_setfam_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48           ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.48             ( v3_setfam_1 @ C @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48          ( ![C:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48              ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.48                ( v3_setfam_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t62_setfam_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d13_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((r2_hidden @ X5 @ X6)
% 0.21/0.48          | (v3_setfam_1 @ X6 @ X5)
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.48      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.21/0.48  thf('2', plain, (((v3_setfam_1 @ sk_C @ sk_A) | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, (~ (v3_setfam_1 @ sk_C @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t3_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X9 : $i, X11 : $i]:
% 0.21/0.48         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('9', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(cc1_subset_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.48          | (v1_xboole_0 @ X3)
% 0.21/0.48          | ~ (v1_xboole_0 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.48  thf('11', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(t4_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.21/0.48          | (m1_subset_1 @ X12 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain, ((m1_subset_1 @ sk_A @ sk_B_1)),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf(t2_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r2_hidden @ X7 @ X8)
% 0.21/0.48          | (v1_xboole_0 @ X8)
% 0.21/0.48          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.48  thf('18', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (v3_setfam_1 @ X6 @ X5)
% 0.21/0.48          | ~ (r2_hidden @ X5 @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.48      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ sk_B_1) | ~ (v3_setfam_1 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, ((v3_setfam_1 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.48      inference('clc', [status(thm)], ['18', '23'])).
% 0.21/0.48  thf('25', plain, ((v1_xboole_0 @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '24'])).
% 0.21/0.48  thf('26', plain, ($false), inference('demod', [status(thm)], ['6', '25'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
