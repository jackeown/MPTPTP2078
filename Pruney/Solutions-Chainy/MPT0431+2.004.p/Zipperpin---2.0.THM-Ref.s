%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mCWjvi4H59

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:37 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  392 ( 814 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t63_setfam_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v3_setfam_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v3_setfam_1 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
             => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v3_setfam_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v3_setfam_1 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
               => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_setfam_1 @ X23 @ X22 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X17 @ X16 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v3_setfam_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('11',plain,
    ( ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_setfam_1 @ X23 @ X22 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['23','28'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['4','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mCWjvi4H59
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 119 iterations in 0.116s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.57  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.35/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(t63_setfam_1, conjecture,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.35/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.35/0.57                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.35/0.57               ( v3_setfam_1 @
% 0.35/0.57                 ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.57    (~( ![A:$i]:
% 0.35/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.57          ( ![B:$i]:
% 0.35/0.57            ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.35/0.57                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.35/0.57              ( ![C:$i]:
% 0.35/0.57                ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.35/0.57                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.35/0.57                  ( v3_setfam_1 @
% 0.35/0.57                    ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t63_setfam_1])).
% 0.35/0.57  thf('0', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(d13_setfam_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.57       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      (![X22 : $i, X23 : $i]:
% 0.35/0.57         (~ (v3_setfam_1 @ X23 @ X22)
% 0.35/0.57          | ~ (r2_hidden @ X22 @ X23)
% 0.35/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.35/0.57      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      ((~ (r2_hidden @ sk_A @ sk_C) | ~ (v3_setfam_1 @ sk_C @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.57  thf('3', plain, ((v3_setfam_1 @ sk_C @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.35/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(dt_k4_subset_1, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.58       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.58  thf('7', plain,
% 0.35/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.35/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.35/0.58          | (m1_subset_1 @ (k4_subset_1 @ X17 @ X16 @ X18) @ 
% 0.35/0.58             (k1_zfmisc_1 @ X17)))),
% 0.35/0.58      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.35/0.58  thf('8', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0) @ 
% 0.35/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.35/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.58  thf('9', plain,
% 0.35/0.58      ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.35/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.35/0.58  thf('10', plain,
% 0.35/0.58      (![X22 : $i, X23 : $i]:
% 0.35/0.58         ((r2_hidden @ X22 @ X23)
% 0.35/0.58          | (v3_setfam_1 @ X23 @ X22)
% 0.35/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.35/0.58      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.35/0.58  thf('11', plain,
% 0.35/0.58      (((v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.35/0.58         sk_A)
% 0.35/0.58        | (r2_hidden @ sk_A @ 
% 0.35/0.58           (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.58  thf('12', plain,
% 0.35/0.58      (~ (v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.35/0.58          sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('13', plain,
% 0.35/0.58      ((r2_hidden @ sk_A @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C))),
% 0.35/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.35/0.58  thf('14', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('15', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.35/0.58  thf('16', plain,
% 0.35/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.35/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.35/0.58          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.35/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.35/0.58  thf('17', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0)
% 0.35/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.35/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.58  thf('18', plain,
% 0.35/0.58      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)
% 0.35/0.58         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.35/0.58      inference('sup-', [status(thm)], ['14', '17'])).
% 0.35/0.58  thf('19', plain, ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.35/0.58      inference('demod', [status(thm)], ['13', '18'])).
% 0.35/0.58  thf(t98_xboole_1, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.35/0.58  thf('20', plain,
% 0.35/0.58      (![X10 : $i, X11 : $i]:
% 0.35/0.58         ((k2_xboole_0 @ X10 @ X11)
% 0.35/0.58           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.58  thf(t1_xboole_0, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.35/0.58       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.35/0.58  thf('21', plain,
% 0.35/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.58         ((r2_hidden @ X6 @ X7)
% 0.35/0.58          | (r2_hidden @ X6 @ X8)
% 0.35/0.58          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.35/0.58  thf('22', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.35/0.58          | (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.58          | (r2_hidden @ X2 @ X1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.58  thf('23', plain,
% 0.35/0.58      (((r2_hidden @ sk_A @ sk_B)
% 0.35/0.58        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.35/0.58  thf('24', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('25', plain,
% 0.35/0.58      (![X22 : $i, X23 : $i]:
% 0.35/0.58         (~ (v3_setfam_1 @ X23 @ X22)
% 0.35/0.58          | ~ (r2_hidden @ X22 @ X23)
% 0.35/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.35/0.58      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.35/0.58  thf('26', plain,
% 0.35/0.58      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.58  thf('27', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('28', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.35/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.35/0.58  thf('29', plain, ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))),
% 0.35/0.58      inference('clc', [status(thm)], ['23', '28'])).
% 0.35/0.58  thf(d5_xboole_0, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.35/0.58       ( ![D:$i]:
% 0.35/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.35/0.58  thf('30', plain,
% 0.35/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.35/0.58          | (r2_hidden @ X4 @ X1)
% 0.35/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.35/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.35/0.58  thf('31', plain,
% 0.35/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.35/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.35/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.35/0.58  thf('32', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.35/0.58      inference('sup-', [status(thm)], ['29', '31'])).
% 0.35/0.58  thf('33', plain, ($false), inference('demod', [status(thm)], ['4', '32'])).
% 0.35/0.58  
% 0.35/0.58  % SZS output end Refutation
% 0.35/0.58  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
