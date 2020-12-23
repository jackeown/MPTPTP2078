%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UPGAiZhNAS

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 154 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 (1289 expanded)
%              Number of equality atoms :   19 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('6',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( m1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
      | ( X26
        = ( k1_subset_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( r1_tarski @ X22 @ ( k3_subset_1 @ X23 @ X24 ) )
      | ~ ( r1_tarski @ X24 @ ( k3_subset_1 @ X23 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('29',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('35',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','33','34'])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UPGAiZhNAS
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 125 iterations in 0.057s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.51  thf(t40_subset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.21/0.51         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51          ( ( ( r1_tarski @ B @ C ) & 
% 0.21/0.51              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.21/0.51            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.21/0.51  thf('0', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d5_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf(t106_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.51       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.21/0.51  thf('6', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(d1_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X11 @ X12)
% 0.21/0.51          | (r2_hidden @ X11 @ X13)
% 0.21/0.51          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         ((r2_hidden @ X11 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X11 @ X12))),
% 0.21/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.51  thf('9', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.51  thf(d2_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X16 @ X17)
% 0.21/0.51          | (m1_subset_1 @ X16 @ X17)
% 0.21/0.51          | (v1_xboole_0 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.21/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf(t38_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.51         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X26 @ (k3_subset_1 @ X25 @ X26))
% 0.21/0.51          | ((X26) = (k1_subset_1 @ X25))
% 0.21/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.21/0.51  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('17', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X26 @ (k3_subset_1 @ X25 @ X26))
% 0.21/0.51          | ((X26) = (k1_xboole_0))
% 0.21/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.51  thf('20', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf('21', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t35_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.21/0.51             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.21/0.51          | (r1_tarski @ X22 @ (k3_subset_1 @ X23 @ X24))
% 0.21/0.51          | ~ (r1_tarski @ X24 @ (k3_subset_1 @ X23 @ X22))
% 0.21/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.21/0.51          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.21/0.51          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.51  thf('29', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.51  thf('30', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t1_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51       ( r1_tarski @ A @ C ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.21/0.51          | ~ (r1_tarski @ X9 @ X10)
% 0.21/0.51          | (r1_tarski @ X8 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.51  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.51  thf('35', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '33', '34'])).
% 0.21/0.51  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
