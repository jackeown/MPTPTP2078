%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AsDOWsPdaH

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  227 ( 557 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v3_setfam_1 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
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

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_setfam_1 @ X9 @ X8 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['18','23'])).

thf('25',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['11','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['6','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AsDOWsPdaH
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 60 iterations in 0.022s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(t62_setfam_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47       ( ![C:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47           ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.19/0.47             ( v3_setfam_1 @ C @ A ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47          ( ![C:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47              ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.19/0.47                ( v3_setfam_1 @ C @ A ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t62_setfam_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d13_setfam_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         ((r2_hidden @ X8 @ X9)
% 0.19/0.47          | (v3_setfam_1 @ X9 @ X8)
% 0.19/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.47      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.19/0.47  thf('2', plain, (((v3_setfam_1 @ sk_C @ sk_A) | (r2_hidden @ sk_A @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf('3', plain, (~ (v3_setfam_1 @ sk_C @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('4', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.19/0.47      inference('clc', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf(t7_boole, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_boole])).
% 0.19/0.47  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf('7', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t3_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X12 : $i, X14 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.47  thf('9', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf(cc1_subset_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.19/0.47          | (v1_xboole_0 @ X6)
% 0.19/0.47          | ~ (v1_xboole_0 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.47  thf('11', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.19/0.47      inference('clc', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf(t4_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X15 @ X16)
% 0.19/0.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.19/0.47          | (m1_subset_1 @ X15 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain, ((m1_subset_1 @ sk_A @ sk_B)),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.19/0.47  thf(d2_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X2 @ X3)
% 0.19/0.47          | (r2_hidden @ X2 @ X3)
% 0.19/0.47          | (v1_xboole_0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.47  thf('18', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (v3_setfam_1 @ X9 @ X8)
% 0.19/0.47          | ~ (r2_hidden @ X8 @ X9)
% 0.19/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.47      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf('22', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('23', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.19/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain, ((v1_xboole_0 @ sk_B)),
% 0.19/0.47      inference('clc', [status(thm)], ['18', '23'])).
% 0.19/0.47  thf('25', plain, ((v1_xboole_0 @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['11', '24'])).
% 0.19/0.47  thf('26', plain, ($false), inference('demod', [status(thm)], ['6', '25'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
